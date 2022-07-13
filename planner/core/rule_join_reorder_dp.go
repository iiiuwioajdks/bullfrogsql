// Copyright 2018 PingCAP, Inc.
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
	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
	"math/bits"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

/*
基于 DP 的 Join Reorder 算法：

1、使用数字的二进制表示来代表当前参与 Join 的节点情况。11（二进制表示为 1011）表示当前的 Join Group 包含了第 3 号节点，
第 1 号节点和第 0 号节点（节点从 0 开始计数）。

2、f[11] 来表示包含了节点 3, 1, 0 的最优的 Join Tree。

3、转移方程则是 f[group] = min{join{f[sub], f[group ^ sub])} 这里 sub 是 group 二进制表示下的任意子集。
*/
func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.

	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.
	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
		cost := s.baseNodeCumCost(node)
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       node,
			cumCost: cost,
		})
	}
	adjacents := make([][]int, len(s.curJoinGroup))
	totalEqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	addEqEdge := func(lIdx, rIdx int, sf *expression.ScalarFunction) {
		// 构建边界
		totalEqEdges = append(totalEqEdges, joinGroupEqEdge{
			nodeIDs: []int{lIdx, rIdx},
			edge:    sf,
		})
		// 建二维图， 比如 lidx，ridx = 1，2， 则有 adjacents[1] = []int{2}
		adjacents[lIdx] = append(adjacents[lIdx], rIdx)
		adjacents[rIdx] = append(adjacents[rIdx], lIdx)
	}
	// 1、处理等值条件：
	// eqConds 就是 某一列 = 某一列，比如 s.a = t.b, 参数就是 a，b 两列，cond 就是 eq(a,b)
	for _, cond := range eqConds {
		sf := cond.(*expression.ScalarFunction)
		lcol := sf.GetArgs()[0].(*expression.Column)
		rcol := sf.GetArgs()[1].(*expression.Column)
		//fmt.Println("cond : ",cond)
		//fmt.Println("lcol : ",lcol)
		//fmt.Println("rcol : ",rcol)
		lIdx, err := findNodeIndexInGroup(joinGroup, lcol)
		if err != nil {
			return nil, err
		}
		rIdx, err := findNodeIndexInGroup(joinGroup, rcol)
		if err != nil {
			return nil, err
		}
		// 以等值条件构建图
		addEqEdge(lIdx, rIdx, sf)
	}

	// 2、处理非等值条件：
	totalNonEqEdge := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	for _, cond := range s.otherConds {
		// 拿出 cond 的所有列
		columns := expression.ExtractColumns(cond)
		ids := make([]int, 0, len(columns))
		mask := uint(0)
		for _, column := range columns {
			idx, err := findNodeIndexInGroup(joinGroup, column)
			if err != nil {
				return nil, err
			}
			ids = append(ids, idx)
			mask |= 1 << uint(idx)
		}
		totalNonEqEdge = append(totalNonEqEdge, joinGroupNonEqEdge{
			nodeIDs:    ids,
			nodeIDMask: mask,
			expr:       cond,
		})
	}
	visited := make([]bool, len(joinGroup))
	/*之所以使用nodeID2VisitID和visitID2nodeID来映射nodeID和visitID的关系是因为:
	在bfs中并不是每个节点都会被访问，所以len(visit ID) <= len(node ID)。
	nodeID2VisitID 将每个节点被访问的顺序存储在 bfs 中。
	这在 dpGrpah 中用于将 nodeID 掩码转换为 visitID 掩码。
	*/
	nodeID2VisitedID := make([]int, len(joinGroup))
	var joins []LogicalPlan
	// 利用 bfs 找到几个强连通分量, 针对每个子图，利用 dp 找到最优 join 顺序
	for i := 0; i < len(joinGroup); i++ {
		if visited[i] {
			continue
		}
		// visitID2NodeID 就是找到的连通的一个子图
		// 在bfs中被访问的所有节点，也就是所有可以从joinGroup[i]到达的节点
		// 广搜
		visitID2NodeID := s.bfsGraph(i, visited, adjacents, nodeID2VisitedID)
		nodeIDMask := uint(0)
		for _, id := range visitID2NodeID {
			nodeIDMask |= 1 << uint(id)
		}

		// 通过反向顺序进行迭代，可以更快地从totalNonEqEdges中移除nonEqEdge。
		// 找寻该子图的边
		var subNonEqEdges []joinGroupNonEqEdge
		for i := len(totalNonEqEdge) - 1; i >= 0; i-- {
			// 如果这条边不是当前子图的子集就跳过
			if totalNonEqEdge[i].nodeIDMask&nodeIDMask != totalNonEqEdge[i].nodeIDMask {
				continue
			}
			newMask := uint(0)
			for _, nodeId := range totalNonEqEdge[i].nodeIDs {
				newMask |= 1 << uint(nodeID2VisitedID[nodeId])
			}
			totalNonEqEdge[i].nodeIDMask = newMask
			subNonEqEdges = append(subNonEqEdges, totalNonEqEdge[i])
			totalNonEqEdge = append(totalNonEqEdge[:i], totalNonEqEdge[i+1:]...)
		}
		// 对每个子图做 DP,找到最优 join 顺序
		join, err := s.dpGraph(visitID2NodeID, nodeID2VisitedID, joinGroup, totalEqEdges, subNonEqEdges)
		if err != nil {
			return nil, err
		}
		joins = append(joins, join)
	}

	// 将 joins 处理成 执行顺序 并返回
	remainedOtherConds := make([]expression.Expression, 0, len(totalNonEqEdge))
	for _, edge := range totalNonEqEdge {
		remainedOtherConds = append(remainedOtherConds, edge.expr)
	}
	return s.makeBushyJoin(joins, remainedOtherConds), nil
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

// bfs 从 i 开始的子图。 并重新标记其标签以备将来使用。
func (s *joinReorderDPSolver) bfsGraph(i int, visited []bool, adjacents [][]int, nodeID2VisitID []int) []int {
	queue := []int{i}
	visited[i] = true
	var visitID2NodeID []int
	for len(queue) > 0 {
		// 记录下 nodeID <-> visitID
		curId := queue[0]
		// nodeID2VisitID 记录的 visitID是顺序，因此使用 len
		nodeID2VisitID[curId] = len(visitID2NodeID)
		visitID2NodeID = append(visitID2NodeID, curId)
		queue = queue[1:]
		// 在这个节点接着往后走图
		for _, id := range adjacents[curId] {
			if visited[id] {
				continue
			}
			queue = append(queue, id)
			visited[id] = true
		}
	}
	return visitID2NodeID
}

// dpGraph : 它实现了传统的连接重排算法。使用以下公式按子集进行DP:
// bestPlan[S:set of node] = the best one among Join(bestPlan[S1:subset of S], bestPlan[S2: S/S1])
func (s *joinReorderDPSolver) dpGraph(visitID2NodeID []int, nodeID2VisitedID []int, joinGroup []LogicalPlan, totalEqEdges []joinGroupEqEdge, subNonEqEdges []joinGroupNonEqEdge) (LogicalPlan, error) {
	nodeCnt := uint(len(visitID2NodeID))
	bestPlan := make([]*jrNode, 1<<nodeCnt)
	for i := uint(0); i < nodeCnt; i++ {
		// 对应初始化边界条件
		// plan 用二进制表示，比如 1101 表示 join 3，2，0
		bestPlan[1<<i] = s.curJoinGroup[visitID2NodeID[i]]
	}
	// 从小到大枚举nodeBitmap，如果S1属于S2，需要确保S1必须在S2之前被枚举。
	for nodeBitmap := uint(1); nodeBitmap < (1 << nodeCnt); nodeBitmap++ {
		// 自底向上
		// 去掉 2 的 n 次方，因为存放的是 边界条件
		if bits.OnesCount(nodeBitmap) == 1 {
			continue
		}
		// 迭代所有子集
		for sub := (nodeBitmap - 1) & nodeBitmap; sub > 0; sub = (sub - 1) & nodeBitmap {
			remain := nodeBitmap ^ sub
			if sub > remain {
				continue
			}
			// 如果这个子集没有连接，就跳过它。
			if bestPlan[sub] == nil || bestPlan[remain] == nil {
				continue
			}
			// 得到连接两部分的边缘 edge
			eqEdges, otherConds := s.nodesAreConnected(sub, remain, totalEqEdges, subNonEqEdges, nodeID2VisitedID)
			if len(eqEdges) == 0 {
				continue
			}
			join, err := s.newJoinWithEdge(bestPlan[sub].p, bestPlan[remain].p, eqEdges, otherConds)
			if err != nil {
				return nil, err
			}
			cost := s.calcJoinCumCost(join, bestPlan[sub], bestPlan[remain])
			if bestPlan[nodeBitmap] == nil {
				bestPlan[nodeBitmap] = &jrNode{
					p:       join,
					cumCost: cost,
				}
			} else if bestPlan[nodeBitmap].cumCost > cost {
				bestPlan[nodeBitmap].p = join
				bestPlan[nodeBitmap].cumCost = cost
			}
		}
	}
	return bestPlan[(1<<nodeCnt)-1].p, nil
}

func (s *joinReorderDPSolver) nodesAreConnected(subMask, remainMask uint, totalEqEdges []joinGroupEqEdge, totalNonEqEdges []joinGroupNonEqEdge, oldPos2NewPos []int) ([]joinGroupEqEdge, []expression.Expression) {
	var (
		eqEdges    []joinGroupEqEdge
		otherConds []expression.Expression
	)
	// 等值条件：
	for _, edge := range totalEqEdges {
		// 将 nodeId 转为 visitId
		lIdx := uint(oldPos2NewPos[edge.nodeIDs[0]])
		rIdx := uint(oldPos2NewPos[edge.nodeIDs[1]])
		if (subMask&(1<<lIdx)) > 0 && (remainMask&(1<<rIdx)) > 0 || ((subMask&(1<<rIdx)) > 0 && (remainMask&(1<<lIdx)) > 0) {
			eqEdges = append(eqEdges, edge)
		}
	}
	// 非等值条件：
	for _, edge := range totalNonEqEdges {
		// If the result is false, means that the current group hasn't covered the columns involved in the expression.
		if edge.nodeIDMask&(subMask|remainMask) != edge.nodeIDMask {
			continue
		}
		// Check whether this expression is only built from one side of the join.
		if edge.nodeIDMask&subMask == 0 || edge.nodeIDMask&remainMask == 0 {
			continue
		}
		otherConds = append(otherConds, edge.expr)
	}
	return eqEdges, otherConds
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
