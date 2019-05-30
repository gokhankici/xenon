#!/usr/bin/env python3.6
# vim: set foldmethod=marker:

import sys
import warnings
import networkx       as nx
import collections
import cplex
import subprocess
import time
import itertools
import enum

from   flow_capacity import CplexFlowCapSolver
from   utils         import *
from   tests         import get_test

import pdb

class VariableType(enum.Enum):
    EDGE = enum.auto()   # represents a regular edge from the graph
    NODE = enum.auto()   # a node that is ok to mark as always_eq

class Variable:
    """
    These are the stuff that used as a variable in the MILP formulation.
    """
    def __init__(self, variable, index = 0):
        self._variable = variable
        self._index    = index

        if type(variable) == tuple and \
           len(variable) == 2 and \
           type(variable[0]) == type(variable[1]) == int:
            self._variable_type = VariableType.EDGE
        elif type(variable) == int:
            self._variable_type = VariableType.NODE
        else:
            raise Exception("Variable accepts a pair of integers or an integer")

    def get_index(self):
        return self._index

    def is_node(self):
        return self._variable_type == VariableType.NODE

    def is_edge(self):
        return self._variable_type == VariableType.EDGE

    def get_node(self):
        if self.is_node():
            return self._variable
        else:
            raise Exception("Cannot call get_node for a variable of type {}".format(self.variable_type))

    def get_edge(self):
        if self.is_edge():
            return self._variable
        else:
            raise Exception("Cannot call get_edge for a variable of type {}".format(self.variable_type))

    def __eq__(self, other):
        return isinstance(other, Variable) and \
            self._variable      == other._variable and \
            self._variable_type == other._variable_type

    def __hash__(self):
        return hash((self._variable, self._variable_type))

    def __str__(self):
        return "Variable({}, type = {}, index = {})".format(self._variable,
                                                            self._variable_type,
                                                            self._index)

class AssumptionSolver:
    def __init__(self, orig_g, must_eq, cannot_mark_eq):
        """
        Calculate the edge capacities and costs for every node.
        """
        # must_eq, cannot_mark_eq : [Node]
        self.must_eq        = set(must_eq)        # nodes we DO     want to be      "always_eq"
        self.cannot_mark_eq = set(cannot_mark_eq) # nodes we DO NOT want to mark as "always_eq"

        # assign flow capacities to the edges
        cc = CplexFlowCapSolver().get_edge_capacities(orig_g)
        # cap : Node x Node -> Int
        self.cap = cc.capacities
        self.g   = cc.new_graph

        # FIXME: this needs to be removed later ...
        assert(len(cc.extra_nodes) == 0)
        # TODO: is this right ?
        non_markable_nodes = self.cannot_mark_eq

        # nodes that can be marked
        self.markable_nodes = set( v
                                   for v in self.g.nodes()
                                   if v not in non_markable_nodes and len(self.g.succ[v]) > 0 )

        # variables used in the linear problem
        # mapping from variable identifier to the variable itself
        self.variables = { v : Variable(v, n)
                           for n, v in enumerate(itertools.chain(self.g.edges(),
                                                                 self.markable_nodes)) }

        # variable index -> variable
        self.inv_variables = { var.get_index() : var for var in self.variables.values() }

        # calculate costs of the nodes
        # node_costs : Node -> Int
        self.node_costs = self.calc_costs()

    def calc_costs(self):
        """
        Returns a mapping from node ids to their costs
        """
        costs    = collections.defaultdict(int)
        worklist = collections.deque(v for v in self.markable_nodes if len(self.g.pred[v]) == 0)
        done     = set(worklist)

        while worklist:
            v = worklist.popleft()
            costs[v] = max((costs[u] for u in self.g.predecessors(v)), default=0) + 1
            for u in self.g.successors(v):
                if u not in done:
                    worklist.append(u)
                    done.add(u)

        return costs

class CplexAssumptionSolver(AssumptionSolver):
    AlwaysEqConstraint = collections.namedtuple("AlwaysEqConstraint", ["variable", "value"])
    MaxFlowConstraint  = collections.namedtuple("MaxFlowConstraint", ["lhs", "rhs"])

    def __init__(self, filename):
        """
        Parse the given json file that contains the problem description.
        """
        parsed = parse_cplex_input(filename)
        super(CplexAssumptionSolver, self).__init__(parsed["graph"],
                                                    parsed["must_eq"],
                                                    parsed["cannot_mark_eq"])
        self.orig_g    = parsed["graph"]
        self.names     = parsed["names"]
        self.inv_names = parsed["inv_names"]

    def get_always_eq_constraints(self):
        """
        Returns a list of AlwaysEqConstraint
        variable : the outgoing edge of every node in the must_eq set
        value    : the capacity of that edge
        """
        constraints = []
        for var in self.variables.values():
            if var.is_edge() and var.get_edge()[0] in self.must_eq:
                c = CplexAssumptionSolver.\
                    AlwaysEqConstraint(variable = var,
                                       value = self.cap[var.get_edge()])
                constraints.append(c)
        return constraints

    @staticmethod
    def add_always_eq_constraint(prob, c):
        prob.linear_constraints.add(lin_expr = [ cplex.SparsePair(ind = [c.variable.get_index()],
                                                                  val = [1]) ],
                                    senses   = "E",
                                    rhs      = [ c.value ])

    def get_max_flow_constraints(self):
        """
        Returns a list of MaxFlowConstraint
        lhs : incoming nodes
        rhs : outgoing nodes
        """
        constraints = []
        for v in self.g.nodes():
            # if v is a leaf node, skip this step
            if self.g.out_degree(v) == 0:
                continue

            lhs, rhs = [], []

            if v in self.markable_nodes:
                lhs.append( self.variables[v] )
            elif self.g.in_degree(v) == 0:
                # if v is a non-markable root node, skip this step
                continue

            lhs.extend( self.variables[u,v] for u in self.g.predecessors(v) )
            rhs.extend( self.variables[v,w] for w in self.g.successors(v)   )

            c = CplexAssumptionSolver.\
                MaxFlowConstraint(lhs = lhs, rhs = rhs)
            constraints.append(c)
        return constraints

    @staticmethod
    def add_max_flow_constraint(prob, c):
        indices = [ var.get_index() for var in itertools.chain(c.lhs, c.rhs) ]
        coefficients = ( [-1] * len(c.lhs) ) + ( [1] * len(c.rhs) )
        prob.linear_constraints.add(lin_expr = [ cplex.SparsePair(ind = indices,
                                                                  val = coefficients) ],
                                    senses   = "E",
                                    rhs      = [0])

    def get_objective_function(self):
        """
        Return a list that contains the cost of each variable used
        """
        obj = [0] * len(self.variables)
        for var in self.variables.values():
            i = var.get_index()
            if var.is_node():
                obj[i] = self.node_costs[var.get_node()]
            elif var.is_edge():
                obj[i] = 0
            else:
                raise Exception()
        return obj

    def get_upper_bounds(self):
        """
        Return a list that contains the upper bound of each variable used
        """
        ub  = [0] * len(self.variables)
        for var in self.variables.values():
            i = var.get_index()
            if var.is_node():
                n = var.get_node()
                ub[i]  = sum( self.cap[u] for u in self.g.out_edges(n) )
            elif var.is_edge():
                ub[i]  = self.cap[var.get_edge()]
            else:
                raise Exception()
        return ub

    def suggest_assumptions(self):
        """
        Returns a set of nodes that when marked as always_eq, they make the
        nodes in must_eq to be always_eq as well.
        """
        prob = cplex.Cplex()
        prob.set_problem_type(prob.problem_type.MILP) # use Mixed Integer Linear Programming solver
        prob.set_results_stream(None)                 # disable results output
        prob.set_log_stream(None)                     # disable logging output

        # objective is to minimize
        prob.objective.set_sense(prob.objective.sense.minimize)

        t0 = time.perf_counter() # start the stopwatch

        obj = self.get_objective_function()
        ub  = self.get_upper_bounds()

        # update cost and upper bound
        prob.variables.add(obj = obj, ub = ub)

        for c in self.get_always_eq_constraints():
            CplexAssumptionSolver.add_always_eq_constraint(prob, c)

        for c in self.get_max_flow_constraints():
            CplexAssumptionSolver.add_max_flow_constraint(prob, c)

        prob.solve()
        sol = prob.solution

        t1 = time.perf_counter()
        print("elapsed time: {} ms".format(int((t1-t0) * 1000)))

        assert(sol.get_method() == sol.method.MIP)
        prob.write("assumptions.lp")

        if sol.get_status() == sol.status.MIP_optimal:
            values = sol.get_values()
            marked_nodes = set( var.get_node()
                                for var in ( self.inv_variables[i]
                                             for i, v in enumerate( int(round(x))
                                                                    for x in values )
                                             if v > 0 )
                                if var.is_node() )

            self.validate_marked_nodes(marked_nodes)

            return marked_nodes
        else:
            print("linprog failed: {}".format(sol.get_status_string()))
            sys.exit(1)

    def validate_marked_nodes(self, marked_nodes):
        g         = self.orig_g
        always_eq = marked_nodes.copy()
        worklist  = set([ w for v in marked_nodes for w in g.succ[v] ])

        def ns(s):
            return set( self.names[n] for n in s )

        while len(worklist) > 0:
            v    = worklist.pop()
            name = self.names[v]

            before = v in always_eq
            after  = all([u in always_eq for u in g.pred[v]])

            if before:
                continue
            elif after:
                always_eq.add(v)
                debug("[+++++] {:35}".format(name))
                worklist.update(set(g.succ[v]))
            else:
                debug("[-----] {:35} : {}".format(name, ", ".join("{}({})".format(self.names[u], "+" if u in always_eq else "-") for u in g.pred[v])))

        print("\n\n\n")
        err = False
        for v in self.must_eq:
            if v not in always_eq:
                print("VALIDATION ERROR: {:<35} IS NOT ALWAYS EQUAL !".format(self.names[v]))
                err = True

        print("Marked nodes:")
        for n in marked_nodes:
            print("  {}".format(self.names[n]))

        if err:
            sys.exit(1)

    def validate_marked_names(self, names):
        self.validate_marked_nodes(set( self.inv_names[n] for n in names ))

    def run(self):
        print("Must equal   :")
        for v in sorted([self.names[v] for v in self.must_eq]):
            print("  {}".format(v))

        marked_nodes = self.suggest_assumptions()
        self.validate_marked_nodes(marked_nodes)

        print("Marked nodes : {}".format(", ".join(self.names[v] for v in marked_nodes)))


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("usage: assumptions.py <cplex.json>")
        sys.exit(1)
    else:
        CplexAssumptionSolver(sys.argv[1]).run()

        # CplexAssumptionSolver(sys.argv[1]).\
        #     validate_marked_names([
        #         "palu_ivalid",
        #         "id_subclass",
        #         "id_pw",
        #         "g_resetn",
        #         "id_class"
        #     ])
