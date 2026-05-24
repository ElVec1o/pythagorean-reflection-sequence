"""
G42_mcmullen_bridge.py
======================
Search W(E_m) for m in {10, 11, 12} for elements whose spectral radius
on the root lattice equals one of our r_n values:

  r_2 = phi          ~ 1.618034
  r_3 = 2            (exact)
  r_4 = 1+2cos(2pi/7)~ 2.246980
  r_5 = 1+sqrt(2)    ~ 2.414214
  r_6 = 1+2cos(2pi/9)~ 2.532089

Reflections on a root lattice with Cartan matrix C act as
    s_i(x) = x - <x, alpha_i^v> alpha_i,
or in the standard simple-root basis,
    s_i = I - e_i (C row i)^T,
i.e. (s_i)_{jk} = delta_{jk} - delta_{ji} C_{ik}.

We enumerate short words in the simple reflections (up to a length bound)
and inspect the spectral radii of the resulting matrices.
"""

from __future__ import annotations
import itertools
import numpy as np
import sympy as sp
from collections import defaultdict

# ---------- Cartan matrices ----------------------------------------------------

def cartan_E(n: int) -> np.ndarray:
    """
    Cartan matrix of E_n for n in {6,7,8,9,10,11,12}.
    Numbering: node 1 is the branch node, attached to 2 (T-leg of length 2)
    and to the chain 3-4-...-n; node 2 is the short tip.

    More concretely we use the Bourbaki-style E_n:
        1 - 3 - 4 - 5 - ... - n
                |
                2
    i.e. node 2 attaches to node 4 (the standard "trivalent" vertex).
    For arbitrary n we use this T-shape:

        s1 - s3 - s4 - ... - sn
                  |
                  s2

    This matches the E_n / T_{2,3,n-3} Coxeter graphs.
    """
    C = 2 * np.eye(n, dtype=int)
    # chain 1-3-4-...-n
    chain = [1] + list(range(3, n + 1))
    for a, b in zip(chain, chain[1:]):
        C[a - 1, b - 1] = -1
        C[b - 1, a - 1] = -1
    # branch: 2 - 4
    C[1, 3] = -1
    C[3, 1] = -1
    return C


def simple_reflections(C: np.ndarray):
    n = C.shape[0]
    S = []
    for i in range(n):
        Si = np.eye(n, dtype=int)
        for k in range(n):
            Si[i, k] -= C[i, k]
        S.append(Si)
    return S


def word(S, indices):
    n = S[0].shape[0]
    M = np.eye(n, dtype=int)
    for i in indices:
        M = M @ S[i]
    return M


# ---------- Target spectral radii ---------------------------------------------

TARGETS = {
    "r2 = phi":          (1 + np.sqrt(5)) / 2,
    "r3 = 2":            2.0,
    "r4 = 1+2cos(2pi/7)":1 + 2*np.cos(2*np.pi/7),
    "r5 = 1+sqrt(2)":    1 + np.sqrt(2),
    "r6 = 1+2cos(2pi/9)":1 + 2*np.cos(2*np.pi/9),
}


def closest_target(rho: float, tol=1e-6):
    best = None
    for name, val in TARGETS.items():
        d = abs(rho - val)
        if d < tol and (best is None or d < best[1]):
            best = (name, d, val)
    return best


def spectral_radius(M: np.ndarray) -> float:
    w = np.linalg.eigvals(M.astype(float))
    return float(np.max(np.abs(w)))


# ---------- Brute-force word search -------------------------------------------

def search(n_E: int, max_len: int, only_reduced: bool = True, log_every=2):
    print(f"\n=== W(E_{n_E}): brute word search up to length {max_len} ===")
    C = cartan_E(n_E)
    S = simple_reflections(C)

    seen_rho = defaultdict(list)  # rho rounded -> example word
    hits = []

    for L in range(1, max_len + 1):
        count = 0
        for word_indices in itertools.product(range(n_E), repeat=L):
            # cheap reduced-word filter: skip i,i adjacent
            if only_reduced and any(a == b for a, b in zip(word_indices, word_indices[1:])):
                continue
            M = word(S, word_indices)
            rho = spectral_radius(M)
            if rho > 1.001:           # only hyperbolic-type elements
                key = round(rho, 5)
                if not seen_rho[key]:
                    seen_rho[key].append(word_indices)
                hit = closest_target(rho)
                if hit:
                    hits.append((word_indices, rho, hit))
            count += 1
        print(f"  len {L}: scanned {count} reduced words; "
              f"distinct rho>1 so far: {len([k for k in seen_rho if k>1])}")

    # report smallest rho > 1 (the Salem-type element)
    pos = sorted(k for k in seen_rho if k > 1.001)
    print(f"\n  Smallest 8 spectral radii > 1 in W(E_{n_E}):")
    for k in pos[:8]:
        w_ex = seen_rho[k][0]
        print(f"    rho ≈ {k:.6f}   example word  s{w_ex}")

    if hits:
        print(f"\n  !! HITS matching r_n targets:")
        for w, rho, h in hits:
            print(f"    word {w}  rho={rho:.8f}  ->  {h[0]} (val={h[2]:.8f})")
    else:
        print(f"\n  No exact-match hits to any r_n target at this length.")
    return seen_rho, hits


# ---------- Symbolic spectral-radius check via characteristic polynomial -----

def char_poly_factored(M):
    """Return factored characteristic polynomial in sympy."""
    A = sp.Matrix(M.tolist())
    x = sp.symbols('x')
    p = A.charpoly(x).as_expr()
    return sp.factor(p)


def is_target_root(M, target_minimal_poly):
    """Check if char poly of M is divisible by the given minimal polynomial."""
    A = sp.Matrix(M.tolist())
    x = sp.symbols('x')
    p = A.charpoly(x).as_expr()
    q, r = sp.div(p, target_minimal_poly, x)
    return sp.simplify(r) == 0


# Minimal polynomials of the targets (over Z):
def target_min_polys():
    x = sp.symbols('x')
    return {
        "r2 = phi":           x**2 - x - 1,                # phi root of x^2-x-1
        "r3 = 2":             x - 2,
        "r4 = 1+2cos(2pi/7)": x**3 - 3*x**2 + 4,           # check: roots are 1+2cos(2pi k/7)
        # actually min poly of 2cos(2pi/7) is y^3+y^2-2y-1; substituting y=x-1:
        # gives (x-1)^3+(x-1)^2-2(x-1)-1 = x^3 -2x^2 -x +1  -- let's recompute
        "r5 = 1+sqrt(2)":     x**2 - 2*x - 1,
        "r6 = 1+2cos(2pi/9)": None,  # fill in if needed
    }


def fix_target_polys():
    """Recompute correct minimal polynomials."""
    x = sp.symbols('x')
    polys = {}
    # phi:
    polys["r2 = phi"] = sp.Poly(x**2 - x - 1, x)
    # 2:
    polys["r3 = 2"] = sp.Poly(x - 2, x)
    # 1 + 2cos(2pi/7): substitute y = 2cos(2pi/7), min poly of y is y^3+y^2-2y-1
    y = sp.symbols('y')
    py = y**3 + y**2 - 2*y - 1
    pr4 = sp.Poly(py.subs(y, x - 1), x)
    polys["r4 = 1+2cos(2pi/7)"] = pr4
    # 1+sqrt(2): minimal poly x^2 - 2x - 1
    polys["r5 = 1+sqrt(2)"] = sp.Poly(x**2 - 2*x - 1, x)
    # 1 + 2cos(2pi/9): min poly of 2cos(2pi/9) is y^3 - 3y + 1
    py6 = y**3 - 3*y + 1
    pr6 = sp.Poly(py6.subs(y, x - 1), x)
    polys["r6 = 1+2cos(2pi/9)"] = pr6
    return polys


# ---------- Run --------------------------------------------------------------

def coxeter_element_test(n_E: int):
    """Compute the standard Coxeter element c = s1 s2 ... sn and its spectral radius."""
    C = cartan_E(n_E)
    S = simple_reflections(C)
    c = np.eye(n_E, dtype=int)
    for s in S:
        c = c @ s
    rho = spectral_radius(c)
    p = char_poly_factored(c)
    return c, rho, p


def search_parabolic_then_check_targets(n_E: int, max_len: int):
    """
    More targeted search: enumerate words but check whether the
    characteristic polynomial of the resulting element is DIVISIBLE BY
    any of the target minimal polynomials -- not just whether the
    spectral radius matches numerically.

    A reflection-subgroup element of type A_4 inside W(E_n) has
    spec containing 5th roots of unity, so its spectral radius is 1
    (finite order). To get phi as a spectral radius we need an
    infinite-order element whose Mahler measure includes phi.
    """
    print(f"\n=== W(E_{n_E}): target-poly divisibility search up to length {max_len} ===")
    C = cartan_E(n_E)
    S = simple_reflections(C)
    polys = fix_target_polys()
    x = sp.symbols('x')
    hits = []
    rho_dist = defaultdict(list)

    for L in range(2, max_len + 1):
        scanned = 0
        for word_indices in itertools.product(range(n_E), repeat=L):
            # skip trivial reductions s_i s_i
            if any(a == b for a, b in zip(word_indices, word_indices[1:])):
                continue
            scanned += 1
            M = word(S, word_indices)
            rho = spectral_radius(M)
            if rho > 1.0001:
                rho_dist[round(rho, 5)].append(word_indices)
                # only do the symbolic check if rho is close to a target
                for name, val in TARGETS.items():
                    if abs(rho - val) < 1e-3:
                        # Symbolic verification
                        A = sp.Matrix(M.tolist())
                        cp = A.charpoly(x).as_expr()
                        tp = polys[name].as_expr()
                        q, r = sp.div(cp, tp, x)
                        if sp.simplify(r) == 0:
                            hits.append((word_indices, name, rho, sp.factor(cp)))
        print(f"  len {L}: scanned {scanned} reduced words, distinct rho>1 cumulative: {len(rho_dist)}")
        if hits:
            print(f"  HITS so far:")
            for h in hits:
                print(f"    word={h[0]}  target={h[1]}  rho_num={h[2]:.6f}")
                print(f"      char poly factored = {h[3]}")
    # Smallest few:
    keys = sorted(rho_dist.keys())
    print(f"  Smallest 10 numerical spectral radii > 1 found:")
    for k in keys[:10]:
        print(f"    rho≈{k}  e.g. word={rho_dist[k][0]}")
    return hits, rho_dist


if __name__ == "__main__":
    # Sanity polys
    polys = fix_target_polys()
    print("Target minimal polynomials over Z:")
    for k, p in polys.items():
        print(f"  {k:25s} -> {sp.expand(p.as_expr())}")

    # Coxeter element sanity check
    for n in (8, 9, 10, 11):
        c, rho, p = coxeter_element_test(n)
        print(f"\nE_{n} Coxeter element: spectral radius ≈ {rho:.6f}")
        print(f"  char poly factored: {p}")

    # Targeted divisibility search at length up to 8 in E_10 and E_11
    hits, dist = search_parabolic_then_check_targets(10, max_len=7)
    print("\n=== Summary E_10 ===  hits:", len(hits))

    hits11, dist11 = search_parabolic_then_check_targets(11, max_len=6)
    print("\n=== Summary E_11 ===  hits:", len(hits11))
