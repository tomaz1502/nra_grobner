#!/usr/bin/env python3
"""
Parse an SMT-LIB file (QF_NRA fragment) into sympy polynomials and run
Tiwari's procedure from tiwari.py.

Supported assertions: conjunctions of relational atoms (=, <, <=, >, >=)
whose arguments are polynomial expressions over Real-typed constants.
"""

import sys
import io

from pysmt.smtlib.parser import SmtLibParser
import pysmt.operators as op
from pysmt.typing import REAL

import sympy
from sympy import Symbol, Rational, Integer

from tiwari import TiwariSolver


def pysmt_to_sympy(node, sym_table):
    """Recursively convert a pysmt term into a sympy expression."""
    nt = node.node_type()

    if nt == op.SYMBOL:
        name = node.symbol_name()
        if name not in sym_table:
            sym_table[name] = Symbol(name)
        return sym_table[name]

    if nt == op.INT_CONSTANT:
        return Integer(node.constant_value())

    if nt == op.REAL_CONSTANT:
        v = node.constant_value()
        return Rational(v.numerator, v.denominator)

    if nt == op.PLUS:
        return sum((pysmt_to_sympy(a, sym_table) for a in node.args()), sympy.S.Zero)

    if nt == op.MINUS:
        a, b = node.args()
        return pysmt_to_sympy(a, sym_table) - pysmt_to_sympy(b, sym_table)

    if nt == op.TIMES:
        result = sympy.S.One
        for a in node.args():
            result = result * pysmt_to_sympy(a, sym_table)
        return result

    if nt == op.POW:
        base, exp = node.args()
        return pysmt_to_sympy(base, sym_table) ** pysmt_to_sympy(exp, sym_table)

    if nt == op.DIV:
        a, b = node.args()
        return pysmt_to_sympy(a, sym_table) / pysmt_to_sympy(b, sym_table)

    raise ValueError(f"Unsupported term: {node} (node_type={nt})")


def collect_atoms(formula):
    """Flatten a top-level conjunction into a list of atomic formulas."""
    nt = formula.node_type()
    if nt == op.AND:
        atoms = []
        for a in formula.args():
            atoms.extend(collect_atoms(a))
        return atoms
    return [formula]


def add_atom(solver, atom, sym_table):
    """Translate a single (in)equality atom into a TiwariSolver constraint."""
    nt = atom.node_type()
    args = atom.args()

    if nt == op.OR:
        raise ValueError(f"Disjunctions not supported: {atom}")

    if nt == op.NOT:
        inner = args[0]
        if inner.node_type() == op.EQUALS:
            raise ValueError(f"Disequalities not supported: {atom}")
        raise ValueError(f"Unsupported negation: {atom}")

    if len(args) != 2:
        raise ValueError(f"Unsupported atom: {atom}")

    lhs = pysmt_to_sympy(args[0], sym_table)
    rhs = pysmt_to_sympy(args[1], sym_table)

    if nt == op.EQUALS:
        solver.add_eq(lhs - rhs)
    elif nt == op.LT:
        # lhs < rhs  <=>  rhs - lhs > 0
        solver.add_gt(rhs - lhs)
    elif nt == op.LE:
        # lhs <= rhs  <=>  rhs - lhs >= 0
        solver.add_ge(rhs - lhs)
    else:
        raise ValueError(f"Unsupported relation: {atom} (node_type={nt})")


def parse_smt2(path):
    """Parse an SMT-LIB file and return a configured TiwariSolver."""
    with open(path) as f:
        script = SmtLibParser().get_script(io.StringIO(f.read()))

    sym_table = {}
    declared = []
    for cmd in script.commands:
        if cmd.name in ('declare-const', 'declare-fun'):
            sym = cmd.args[0]
            if sym.symbol_type() == REAL:
                name = sym.symbol_name()
                s = Symbol(name)
                sym_table[name] = s
                declared.append(s)

    solver = TiwariSolver(declared)

    for cmd in script.filter_by_command_name('assert'):
        for atom in collect_atoms(cmd.args[0]):
            add_atom(solver, atom, sym_table)

    return solver


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'ex2.smt2'
    # print(f"Parsing {path}")
    solver = parse_smt2(path)
    result = solver.solve()
    print(f"  => {'UNSAT' if result else 'UNKNOWN'}")


if __name__ == '__main__':
    main()
