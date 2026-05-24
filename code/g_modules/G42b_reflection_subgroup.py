"""
G42b_reflection_subgroup.py
============================
Search for a reflection subgroup of W(E_m) isomorphic to the path
Coxeter group P_n (= our paper's W_n with one infinity edge),
in such a way that the spectral radius of its Coxeter element equals r_n.

Strategy: enumerate roots of W(E_m) and look for tuples
    (alpha_1, ..., alpha_{n+1})
such that the "Cartan-like" matrix of inner products has the shape
of a path with ONE edge labelled infinity, i.e.:

    B(alpha_i, alpha_i) = 2 for all i
    B(alpha_i, alpha_{i+1}) in {-1, -2}  (one of them is -2: the inf-edge)
    B(alpha_i, alpha_j)    = 0           for non-adjacent i,j

If we find such a configuration, then by Deodhar's theorem the subgroup
<s_{alpha_1}, ..., s_{alpha_{n+1}}> is the Coxeter group P_n, its Coxeter
element acts on span<alpha_i>'s with spectral radius r_n, and extends
to W(E_m) by identity on the orthogonal complement -- so r_n is the
spectral radius of an element of W(E_m).

Then, by McMullen's Theorem 1.5, if this element has no periodic roots
(under its action on Phi(E_m)), it is realized by a surface automorphism
of the blowup X_m of P^2 at m very-general points.
"""
from __future__ import annotations
import numpy as np
import itertools
from collections import deque

# ----- E_m root system construction -----------------------------------------

def cartan_E(n: int) -> np.ndarray:
    """E_n Cartan matrix; T-shape: s1-s3-s4-...-sn with s2 attached to s4."""
    C = 2 * np.eye(n, dtype=int)
    chain = [1] + list(range(3, n + 1))
    for a, b in zip(chain, chain[1:]):
        C[a - 1, b - 1] = -1
        C[b - 1, a - 1] = -1
    C[1, 3] = -1
    C[3, 1] = -1
    return C


def simple_reflections(C):
    n = C.shape[0]
    S = []
    for i in range(n):
        Si = np.eye(n, dtype=int)
        for k in range(n):
            Si[i, k] -= C[i, k]
        S.append(Si)
    return S


def enumerate_roots_bfs(n_E: int, max_height: int = 6):
    """
    Enumerate positive roots of W(E_n) by BFS: start from simple roots
    e_i (standard basis), apply simple reflections, keep vectors with
    nonneg coords and B(v,v) = 2. Stop when no new roots at given height.

    The bilinear form in simple-root coordinates is the Cartan matrix C
    (with appropriate sign). For E_n with our convention B(alpha_i,alpha_j)
    = C_{ij} where C is the symmetric Cartan matrix above; but C_{ii}=2,
    C_{ij}=-1 if adjacent, else 0. Then B(v,v) = v^T C v.

    For n=10 the lattice is Lorentzian II_{9,1}: there are infinitely many
    roots. We just enumerate up to a height cap.
    """
    C = cartan_E(n_E)
    S = simple_reflections(C)

    # simple roots: e_i
    simple = [np.eye(n_E, dtype=int)[i] for i in range(n_E)]
    seen = {tuple(v): 0 for v in simple}  # root -> height
    frontier = list(simple)
    height = 0
    while frontier and height < max_height:
        new_frontier = []
        for v in frontier:
            for s in S:
                w = s @ v
                t = tuple(w)
                # only keep positive roots (nonneg in simple basis)
                if all(x >= 0 for x in w) and t not in seen:
                    seen[t] = height + 1
                    new_frontier.append(w)
        frontier = new_frontier
        height += 1
    roots = np.array(list(seen.keys()), dtype=int)
    return C, roots


def bilinear(C, v, w):
    return int(v @ C @ w)


# ----- Path P_n with one infinity edge --------------------------------------
# Profile of inner products for length n+1 path with the i-th edge being inf:
#   B(a_k, a_k) = 2
#   B(a_k, a_{k+1}) = -1 except B(a_{inf}, a_{inf+1}) = -2
#   B(a_k, a_l) = 0 for |k-l| >= 2

def path_profile(n_path: int, inf_edge: int):
    """Return desired (n_path+1)x(n_path+1) inner-product matrix."""
    L = n_path + 1
    P = 2 * np.eye(L, dtype=int)
    for k in range(L - 1):
        val = -2 if k == inf_edge else -1
        P[k, k+1] = val
        P[k+1, k] = val
    return P


def check_configuration(roots, C, indices, P_target):
    """Check whether B(roots[i_a], roots[i_b]) == P_target[a,b] for all a,b."""
    chosen = [roots[i] for i in indices]
    L = len(chosen)
    for a in range(L):
        for b in range(L):
            if bilinear(C, chosen[a], chosen[b]) != P_target[a, b]:
                return False
    return True


def search_subdiagram(n_E: int, n_path: int, max_height: int = 6, max_combos=200000):
    """Look for n_path edges (n_path+1 nodes) embedding P_n in E_m."""
    print(f"\n=== Searching W(E_{n_E}) for P_{n_path} reflection-subdiagram ===")
    C, roots = enumerate_roots_bfs(n_E, max_height=max_height)
    print(f"  enumerated {len(roots)} positive roots up to height {max_height}")

    # Build pairwise inner product table
    R = roots
    nR = len(R)
    G = R @ C @ R.T  # nR x nR
    # All B(r,r) must be 2:
    print(f"  diag values present: {set(G.diagonal().tolist())}")

    # Build per-root neighbour lists by Cartan value
    nbr_m1 = [set() for _ in range(nR)]  # -1 neighbours
    nbr_m2 = [set() for _ in range(nR)]  # -2 neighbours (these give infinity edges)
    for i in range(nR):
        for j in range(nR):
            if i == j: continue
            if G[i, j] == -1: nbr_m1[i].add(j)
            elif G[i, j] == -2: nbr_m2[i].add(j)
    n_inf_edges = sum(len(s) for s in nbr_m2) // 2
    n_simp_edges = sum(len(s) for s in nbr_m1) // 2
    print(f"  among these roots: {n_simp_edges} pairs with B=-1, {n_inf_edges} pairs with B=-2")

    if n_inf_edges == 0 and n_path >= 1:
        # We can't realize an infinity edge unless we extend the root set
        return None

    # For each position of the infinity edge, attempt a DFS path-build
    for inf_pos in range(n_path):
        target = path_profile(n_path, inf_pos)
        # try all (i0, i1) pairs with B(i0,i1) = target[0,1]
        # and continue extending
        L_path = n_path + 1

        # we need ordered tuple (i_0, i_1, ..., i_n) such that
        # B(i_a, i_b) matches target. Equivalently each consecutive pair
        # has the right (-1 or -2) inner product, and every non-consec
        # pair has B=0.
        def dfs(current):
            a = len(current)
            if a == L_path:
                yield tuple(current)
                return
            # require B with each previous = target[a, b]
            # candidates that pass these constraints
            # for performance, iterate over the neighbour list of current[-1]
            if a == 0:
                cand = range(nR)
            else:
                last = current[-1]
                req = target[a, a-1]
                if req == -1:
                    cand = nbr_m1[last]
                elif req == -2:
                    cand = nbr_m2[last]
                else:
                    cand = []
            for j in cand:
                if j in current: continue
                ok = True
                for b in range(a):
                    if G[j, current[b]] != target[a, b]:
                        ok = False; break
                if ok:
                    current.append(j)
                    yield from dfs(current)
                    current.pop()

        found = 0
        for tup in dfs([]):
            found += 1
            if found <= 3:
                rs = [R[k] for k in tup]
                print(f"  FOUND path with inf-edge at position {inf_pos}: indices {tup}")
                print(f"    roots:")
                for k, r in enumerate(rs):
                    print(f"      a_{k} = {r}")
            if found >= 50:
                break
        if found:
            print(f"  Total {found} configurations found (capped at 50) for inf_pos={inf_pos}")
            return ("FOUND", inf_pos, found)
    print("  No subdiagram found.")
    return None


# ----- Coxeter spectral radius of P_n ---------------------------------------

def coxeter_eigvalues_from_profile(P):
    """
    For a Coxeter group given by symmetric "Cartan-like" matrix P
    with diagonal 2 and off-diag 2cos(pi/m_{ij}), the Coxeter element
    matrix in the simple-root basis is the product of the simple
    reflections, s_i(x) = x - (Px)_i e_i.
    We just compute the product.
    """
    L = P.shape[0]
    M = np.eye(L)
    for i in range(L):
        Si = np.eye(L)
        for k in range(L):
            Si[i, k] -= P[i, k]
        M = M @ Si
    eig = np.linalg.eigvals(M)
    return eig


if __name__ == "__main__":
    # Verify our r_n values match P_n Coxeter spectral radii (sanity)
    print("=== Sanity: spectral radii of P_n Coxeter elements ===")
    for n_path in range(2, 8):
        for inf_pos in range(n_path):
            P = path_profile(n_path, inf_pos).astype(float)
            eig = coxeter_eigvalues_from_profile(P)
            rho = np.max(np.abs(eig))
            expected = 1 + 2*np.cos(2*np.pi/(n_path+3)) if n_path >= 2 else None
            print(f"  P_{n_path} inf@{inf_pos}: rho={rho:.6f}"
                  f"  expected r_{n_path}={expected}")

    # Now search E_10 for embeddings; need higher height to get B=-2 pairs
    for h in [8, 12, 16]:
        result = search_subdiagram(10, 2, max_height=h)
        print(f"  result: {result}")
        if result is not None:
            break
