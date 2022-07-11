// Copyright 2015 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"context"
	"math"

	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/infoschema"
	"github.com/pingcap/tidb/parser/ast"
	"github.com/pingcap/tidb/planner/property"
	"github.com/pingcap/tidb/sessionctx"
	"github.com/pingcap/tidb/types"
)

// OptimizeAstNode optimizes the query to a physical plan directly.
var OptimizeAstNode func(ctx context.Context, sctx sessionctx.Context, node ast.Node, is infoschema.InfoSchema) (Plan, types.NameSlice, error)

const (
	flagPrunColumns uint64 = 1 << iota
	flagBuildKeyInfo
	flagEliminateAgg
	flagEliminateProjection
	flagMaxMinEliminate
	flagPredicatePushDown
	flagEliminateOuterJoin
	flagPushDownAgg
	flagPushDownTopN
	flagJoinReOrder
)

var optRuleList = []logicalOptRule{
	&columnPruner{},
	&buildKeySolver{},
	&aggregationEliminator{},
	&projectionEliminator{},
	&maxMinEliminator{},
	&ppdSolver{},
	&outerJoinEliminator{},
	&aggregationPushDownSolver{},
	&pushDownTopNOptimizer{},
	&joinReOrderSolver{},
}

// logicalOptRule means a logical optimizing rule, which contains decorrelate, ppd, column pruning, etc.
type logicalOptRule interface {
	optimize(context.Context, LogicalPlan) (LogicalPlan, error)
	name() string
}

// BuildLogicalPlan used to build logical plan from ast.Node.
func BuildLogicalPlan(ctx context.Context, sctx sessionctx.Context, node ast.Node, is infoschema.InfoSchema) (Plan, types.NameSlice, error) {
	sctx.GetSessionVars().PlanID = 0
	sctx.GetSessionVars().PlanColumnID = 0
	builder := NewPlanBuilder(sctx, is)
	p, err := builder.Build(ctx, node)
	if err != nil {
		return nil, nil, err
	}
	return p, p.OutputNames(), err
}

// DoOptimize optimizes a logical plan to a physical plan.
func DoOptimize(ctx context.Context, flag uint64, logic LogicalPlan) (PhysicalPlan, error) {
	// 逻辑优化主要是基于规则的优化，简称 RBO（rule based optimization）
	logic, err := logicalOptimize(ctx, flag, logic)
	if err != nil {
		return nil, err
	}
	// 物理优化会为逻辑查询计划中的算子选择某个具体的实现，
	// 需要用到一些统计信息，决定哪一种方式代价最低，所以是基于代价的优化 CBO（cost based optimization）
	physical, err := physicalOptimize(logic)
	if err != nil {
		return nil, err
	}
	// postOptimize 实际上是在一些优化之后对执行计划的一些调整，例如去掉多余的 projection 算子
	finalPlan := postOptimize(physical)
	return finalPlan, nil
}

func postOptimize(plan PhysicalPlan) PhysicalPlan {
	plan = eliminatePhysicalProjection(plan)
	plan = injectExtraProjection(plan)
	return plan
}

/*
算子：
DataSource 这个就是数据源，也就是表，select * from t里面的 t。

Selection 选择，例如 select xxx from t where xx = 5里面的 where 过滤条件。

Projection 投影， select c from t里面的取 c 列是投影操作。

Join 连接， select xx from t1, t2 where t1.c = t2.c就是把 t1 t2 两个表做 Join。

逻辑优化规则：
列裁剪 columnPruner ：列裁剪的思想是这样的：对于用不上的列，没有必要读取它们的数据，无谓的浪费 IO 资源。
*/
func logicalOptimize(ctx context.Context, flag uint64, logic LogicalPlan) (LogicalPlan, error) {
	var err error
	// 依次遍历优化规则列表，并对当前的执行计划树尝试优化
	for i, rule := range optRuleList {
		// The order of flags is same as the order of optRule in the list.
		// We use a bitmask to record which opt rules should be used. If the i-th bit is 1, it means we should
		// apply i-th optimizing rule.
		if flag&(1<<uint(i)) == 0 {
			continue
		}
		logic, err = rule.optimize(ctx, logic)
		if err != nil {
			return nil, err
		}
	}
	return logic, err
}

func physicalOptimize(logic LogicalPlan) (PhysicalPlan, error) {
	if _, err := logic.recursiveDeriveStats(); err != nil {
		return nil, err
	}

	preparePossibleProperties(logic)

	prop := &property.PhysicalProperty{
		TaskTp:      property.RootTaskType,
		ExpectedCnt: math.MaxFloat64,
	}

	t, err := logic.findBestTask(prop)
	if err != nil {
		return nil, err
	}
	if t.invalid() {
		return nil, ErrInternal.GenWithStackByArgs("Can't find a proper physical plan for this query")
	}

	err = t.plan().ResolveIndices()
	return t.plan(), err
}

func init() {
	expression.EvalAstExpr = evalAstExpr
}
