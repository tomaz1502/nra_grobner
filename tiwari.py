#!/usr/bin/env python3
"""
Tiwari's algebraic unsatisfiability procedure (CSL 2005),
with Extend1 and Extend3.  Extend2 (introduces a symbolic rational alpha
and works over Q(alpha)) is not implemented.

Given:  {p_i = 0} AND {q_j > 0} AND {r_k >= 0}
Goal:   Detect unsatisfiability over the reals.

Method:
  1. Introduce slack variables to convert inequalities to equalities.
  2. Compute Groebner basis (handles Simplify/Deduce/Delete rules).
  3. Detect: split polynomials whose terms are all positive (or all negative)
     over nonneg variables -- since the sum is 0, each term must be 0.
  4. Witness: a single nonzero monomial in strictly-positive vars -> contradiction.
  5. Extend1: if the leading monomial mu0 of a GB element is a product of
     nonneg variables, introduce a fresh nonneg variable e := mu0.
  6. Extend3: otherwise, name a "square-root-like" power-product nu0 (|nu0| > 1)
     such that nu0^2 * nu0' = mu0 * mu0' for some squarefree nonneg nu0'.
     The fresh variable x' := nu0 is unrestricted (not in V>=0).
  Repeat 2-6 until UNSAT or no progress.
"""

from sympy import Symbol, symbols, Poly, groebner, S, Rational, expand
from itertools import count

VERBOSE = False


class TiwariSolver:
    def __init__(self, variables):
        self.orig_vars = list(variables)
        self.V_pos = set()
        self.V_nonneg = set()
        self.ext_vars = []
        self.slack_vars = []
        self.polys = []
        self.definitions = {}
        self._ext_id = count(1)
        self._v_id = count(1)
        self._w_id = count(1)

    @property
    def all_vars(self):
        return self.orig_vars + self.slack_vars + self.ext_vars

    def add_eq(self, p):
        self.polys.append(expand(p))

    def add_gt(self, q):
        v = Symbol(f'v{next(self._v_id)}')
        self.V_pos.add(v)
        self.V_nonneg.add(v)
        self.slack_vars.append(v)
        self.polys.append(expand(q - v))
        return v

    def add_ge(self, q):
        w = Symbol(f'w{next(self._w_id)}')
        self.V_nonneg.add(w)
        self.slack_vars.append(w)
        self.polys.append(expand(q - w))
        return w

    # -- helpers on monomial tuples (relative to self.all_vars) --

    def _vars_of(self, monom):
        av = self.all_vars
        return {av[i] for i, e in enumerate(monom) if e > 0}

    def _to_expr(self, monom):
        expr = S.One
        for var, exp in zip(self.all_vars, monom):
            if exp:
                expr *= var ** exp
        return expr

    def _is_nonneg(self, monom):
        return self._vars_of(monom).issubset(self.V_nonneg)

    def _is_strictly_pos(self, monom):
        return self._vars_of(monom).issubset(self.V_pos)

    # -- inference rules --

    def _check_witness(self, expr):
        """Witness: single nonzero term c*mu with mu in [V>0]."""
        av = self.all_vars
        p = Poly(expr, *av, domain='QQ')
        d = p.as_dict()
        if len(d) != 1:
            return False
        monom, coeff = next(iter(d.items()))
        return coeff != 0 and self._is_strictly_pos(monom)

    def _try_detect(self, gb_polys):
        """Detect: for every poly whose terms are all positive (or all negative)
        over [V>=0], split it -- each term must individually be zero.
        Returns a list of (index, split_terms) pairs."""
        av = self.all_vars
        candidates = []
        for i, expr in enumerate(gb_polys):
            p = Poly(expr, *av, domain='QQ')
            d = p.as_dict()
            if len(d) <= 1:
                continue
            if not all(self._is_nonneg(m) for m in d):
                continue
            coeffs = list(d.values())
            if all(c > 0 for c in coeffs) or all(c < 0 for c in coeffs):
                terms = [c * self._to_expr(m) for m, c in d.items()]
                candidates.append((i, terms))
        return candidates

    def _try_extend1(self, gb_polys):
        """Extend1: for a GB poly whose leading monomial mu0 is in [V>=0],
        introduce a fresh nonneg variable e = mu0."""
        av = self.all_vars
        existing_defs = set(self.definitions.values())
        for expr in gb_polys:
            p = Poly(expr, *av, domain='QQ')
            if len(p.as_dict()) <= 1:
                continue
            lm = p.LM()
            if not self._is_nonneg(lm):
                continue
            if sum(lm) <= 1:
                continue
            lm_expr = self._to_expr(lm)
            if lm_expr in existing_defs:
                continue
            eid = next(self._ext_id)
            e = Symbol(f'e{eid}')
            self.V_nonneg.add(e)
            self.ext_vars.append(e)
            self.definitions[e] = lm_expr
            self.polys.append(lm_expr - e)
            return e
        return None

    def _try_extend3(self, gb_polys, max_degree=None):
        """Extend3: introduce a fresh unrestricted variable x' = nu0, where
        nu0 is a power-product with |nu0| > 1 satisfying nu0^2 * nu0' = mu0 * mu0'
        for some GB poly with leading monomial mu0, nu0' squarefree over V>=0.

        We pick the minimal such nu0 per polynomial: for each variable i with
        exponent m_i in mu0, n_i = m_i // 2 if i in V>=0 else ceil(m_i / 2).
        The V>=0 case absorbs one extra exponent into nu0' when m_i is odd."""
        av = self.all_vars
        existing_defs = set(self.definitions.values())
        for expr in gb_polys:
            p = Poly(expr, *av, domain='QQ')
            if len(p.as_dict()) <= 1:
                continue
            lm = p.LM()
            n = tuple(
                m_i // 2 if av[i] in self.V_nonneg else (m_i + 1) // 2
                for i, m_i in enumerate(lm)
            )
            if sum(n) <= 1:
                continue
            if max_degree is not None and sum(n) > max_degree:
                continue
            nu_expr = self._to_expr(n)
            if nu_expr in existing_defs:
                continue
            eid = next(self._ext_id)
            x_new = Symbol(f'e{eid}')
            self.ext_vars.append(x_new)
            self.definitions[x_new] = nu_expr
            self.polys.append(nu_expr - x_new)
            return x_new
        return None

    # -- main loop --

    def solve(self, max_rounds=10):
        log = (lambda *a: print(*a)) if VERBOSE else (lambda *_: None)
        log("Tiwari UNSAT procedure (Extend1 only)")
        log(f"  vars : {self.orig_vars}")
        log(f"  V>0  : {sorted(self.V_pos, key=str)}")
        log(f"  V>=0 : {sorted(self.V_nonneg, key=str)}")
        log(f"  polys: {self.polys}")

        for rnd in range(max_rounds):
            av = self.all_vars
            log(f"\n--- Round {rnd} ---")

            gb = groebner(self.polys, *av, order='lex', domain='QQ')
            gb_exprs = list(gb)
            self.polys = list(gb_exprs)
            log(f"  GB: {gb_exprs}")

            # nonzero constant in GB => trivially UNSAT
            for p in gb_exprs:
                pp = Poly(p, *av, domain='QQ')
                if pp.is_ground and not pp.is_zero:
                    log(f"  UNSAT: nonzero constant {p} in GB")
                    return True

            # Witness
            for p in gb_exprs:
                if self._check_witness(p):
                    log(f"  UNSAT (Witness): {p}")
                    return True

            # Detect
            candidates = self._try_detect(gb_exprs)
            if candidates:
                all_terms = []
                for idx, terms in sorted(candidates, key=lambda c: -c[0]):
                    log(f"  Detect: {gb_exprs[idx]}  ->  {terms}")
                    self.polys.pop(idx)
                    self.polys.extend(terms)
                    all_terms.extend(terms)
                for t in all_terms:
                    if self._check_witness(t):
                        log(f"  UNSAT (Witness after Detect): {t}")
                        return True
                continue

            # Extend1
            e = self._try_extend1(gb_exprs)
            if e is not None:
                log(f"  Extend1: {e} := {self.definitions[e]}")
                continue

            # Extend3
            e = self._try_extend3(gb_exprs)
            if e is not None:
                log(f"  Extend3: {e} := {self.definitions[e]}")
                continue

            log("  No rules applicable.")
            return False

        log(f"  Reached max rounds ({max_rounds}).")
        return False


# ======================================================================
# Examples
# ======================================================================

def example_simple():
    """x > 0  and  x < 0  --  immediate contradiction via GB + Detect"""
    print("\n" + "=" * 60)
    print("EXAMPLE: x > 0  /\\  x < 0")
    print("=" * 60)
    x = Symbol('x')
    s = TiwariSolver([x])
    s.add_gt(x)
    s.add_gt(-x)
    return s.solve()


def example_paper_2():
    """Paper Example 2 (p.252): x1^3 = x1, x1*x2 > 1, x2^2 < 1/2
    Detected UNSAT through elimination ideal -- no Extend1 needed."""
    print("\n" + "=" * 60)
    print("EXAMPLE 2 (paper): x1^3 = x1, x1*x2 > 1, x2^2 < 1/2")
    print("=" * 60)
    x1, x2 = symbols('x1 x2')
    s = TiwariSolver([x1, x2])
    s.add_eq(x1**3 - x1)
    s.add_gt(x1 * x2 - 1)
    s.add_gt(-x2**2 + Rational(1, 2))
    return s.solve()


def example_paper_4():
    """Paper Example 4 (p.254): v + w1 = 1, w1*w2 - w1 + 1 = 0
    with v > 0, w1 >= 0, w2 >= 0.  Requires Extend1 to detect UNSAT."""
    print("\n" + "=" * 60)
    print("EXAMPLE 4 (paper): v + w1 - 1 = 0,  w1*w2 - w1 + 1 = 0")
    print("  v > 0,  w1 >= 0,  w2 >= 0")
    print("=" * 60)
    v, w1, w2 = symbols('v w1 w2')
    s = TiwariSolver([])
    s.slack_vars = [v, w1, w2]
    s.V_pos = {v}
    s.V_nonneg = {v, w1, w2}
    s.polys = [v + w1 - 1, w1 * w2 - w1 + 1]
    return s.solve()


def example_quadratic():
    """x^2 + 1 > 0  and  x^2 + 1 < 0"""
    print("\n" + "=" * 60)
    print("EXAMPLE: x^2 + 1 > 0  /\\  x^2 + 1 < 0")
    print("=" * 60)
    x = Symbol('x')
    s = TiwariSolver([x])
    s.add_gt(x**2 + 1)
    s.add_gt(-(x**2 + 1))
    return s.solve()


def example_sum_positive():
    """v1 + v2 + 1 = 0  with  v1 > 0, v2 > 0  --  detected via Detect + Witness"""
    print("\n" + "=" * 60)
    print("EXAMPLE: v1 + v2 + 1 = 0,  v1 > 0,  v2 > 0")
    print("=" * 60)
    v1, v2 = symbols('v1 v2')
    s = TiwariSolver([])
    s.slack_vars = [v1, v2]
    s.V_pos = {v1, v2}
    s.V_nonneg = {v1, v2}
    s.polys = [v1 + v2 + 1]
    return s.solve()


def example_satisfiable():
    """x + y = 3, x > 0, y > 0  --  satisfiable, should return UNKNOWN"""
    print("\n" + "=" * 60)
    print("EXAMPLE (SAT): x + y = 3,  x > 0,  y > 0")
    print("=" * 60)
    x, y = symbols('x y')
    s = TiwariSolver([x, y])
    s.add_eq(x + y - 3)
    s.add_gt(x)
    s.add_gt(y)
    return s.solve()


if __name__ == '__main__':
    examples = [
        example_simple,
        # example_paper_2,
        # example_paper_4,
        # example_quadratic,
        # example_sum_positive,
        # example_satisfiable,
    ]
    results = []
    for ex in examples:
        r = ex()
        label = 'UNSAT' if r else 'UNKNOWN'
        results.append((ex.__doc__.split('--')[0].strip(), label))
        print(f"\n  => {label}")

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    for name, label in results:
        print(f"  [{label:>7s}]  {name}")
