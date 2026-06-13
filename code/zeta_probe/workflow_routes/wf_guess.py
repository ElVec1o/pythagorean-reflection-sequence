#!/usr/bin/env python3
"""
ROUTE A - EXHAUSTIVE GUESS BATTERY for OEIS A396406.
Exact rational arithmetic (Python fractions). 43 terms u_0..u_42.

Tests:
(1) Algebraic equation P(x,F)=0
(2) Holonomic / D-finite recurrence
(3) Constant-coefficient linear recurrence

A HIT is reported ONLY if:
  - the homogeneous linear system is over-determined by margin >= 5
    (#equations - #unknowns >= 5, counting one free scaling),
  - the found relation verifies on EVERY available coefficient.
"""

from fractions import Fraction as Fr

U = [1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,
     11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,
     1127236,1697179,2554961,3848384,5777651,8679441,13031206,19574659,
     29338781,43997388,65932461,98849591,147969934]
N = len(U)           # 43
assert N == 43

# ---------------------------------------------------------------------------
# Exact power-series utilities (truncated to length N).
# ---------------------------------------------------------------------------
def series_mul(a, b, trunc):
    """Multiply two coefficient lists as power series, truncated to `trunc` terms."""
    res = [Fr(0)] * trunc
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        if i >= trunc:
            break
        for j, bj in enumerate(b):
            if i + j >= trunc:
                break
            if bj == 0:
                continue
            res[i + j] += ai * bj
    return res

def series_pow(a, k, trunc):
    """a^k as truncated power series. k>=0."""
    res = [Fr(0)] * trunc
    res[0] = Fr(1)
    base = a[:trunc] + [Fr(0)] * max(0, trunc - len(a))
    base = base[:trunc]
    e = k
    b = base
    # simple repeated squaring
    while e > 0:
        if e & 1:
            res = series_mul(res, b, trunc)
        e >>= 1
        if e > 0:
            b = series_mul(b, b, trunc)
    return res

Fser = [Fr(v) for v in U]   # F(x) coefficients, length N

# Precompute F^j for j=0..6 (enough for dy<=6).
Fpow = {0: [Fr(1)] + [Fr(0)] * (N - 1)}
for j in range(1, 7):
    Fpow[j] = series_mul(Fpow[j - 1], Fser, N)

# ---------------------------------------------------------------------------
# Exact fraction-free nullspace of an integer/rational matrix.
# Returns a basis of the (right) null space as a list of rational vectors,
# plus the rank. We use exact Gaussian elimination over Fractions.
# ---------------------------------------------------------------------------
def nullspace(rows, ncols):
    """rows: list of lists of Fraction (the matrix M, dimension nrows x ncols).
       Returns (rank, list_of_nullspace_basis_vectors)."""
    M = [r[:] for r in rows]
    nrows = len(M)
    pivot_cols = []
    r = 0
    for c in range(ncols):
        # find pivot in column c at/after row r
        piv = None
        for rr in range(r, nrows):
            if M[rr][c] != 0:
                piv = rr
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for rr in range(nrows):
            if rr != r and M[rr][c] != 0:
                f = M[rr][c]
                M[rr] = [a - f * b for a, b in zip(M[rr], M[r])]
        pivot_cols.append(c)
        r += 1
        if r == nrows:
            break
    rank = len(pivot_cols)
    free_cols = [c for c in range(ncols) if c not in pivot_cols]
    basis = []
    for fc in free_cols:
        vec = [Fr(0)] * ncols
        vec[fc] = Fr(1)
        for i, pc in enumerate(pivot_cols):
            vec[pc] = -M[i][fc]
        basis.append(vec)
    return rank, basis

def lcm_denoms(vec):
    from math import gcd
    l = 1
    for x in vec:
        d = x.denominator
        l = l // gcd(l, d) * d
    return l

def to_int_vector(vec):
    """Clear denominators, divide by gcd -> primitive integer vector."""
    from math import gcd
    l = lcm_denoms(vec)
    iv = [int(x * l) for x in vec]
    g = 0
    for x in iv:
        g = gcd(g, abs(x))
    if g == 0:
        return iv
    iv = [x // g for x in iv]
    # normalize sign: first nonzero positive
    for x in iv:
        if x != 0:
            if x < 0:
                iv = [-y for y in iv]
            break
    return iv

# ===========================================================================
# TEST 1: Algebraic equation  P(x, F) = 0,  P = sum_{i<=dx, j<=dy} c_{ij} x^i F^j
# ===========================================================================
def test_algebraic():
    results = []
    hit = None
    for dy in range(2, 7):          # deg in F
        for dx in range(2, 15):     # deg in x
            unknowns = (dx + 1) * (dy + 1)
            if unknowns > 36:
                continue
            # Build series for each monomial x^i * F^j, truncated to N coeffs.
            # Number of usable equations = N (coefficients 0..N-1).
            cols = []   # each col is the coefficient vector (length N) of one monomial
            colinfo = []
            for j in range(dy + 1):
                fj = Fpow[j]
                for i in range(dx + 1):
                    # x^i * F^j : shift fj right by i
                    vec = [Fr(0)] * N
                    for k in range(N):
                        if k - i >= 0:
                            vec[k] = fj[k - i]
                    cols.append(vec)
                    colinfo.append((i, j))
            ncols = len(cols)
            # Matrix M: rows = coefficients (equations), cols = unknown monomial coeffs.
            # M[row][col] = coefficient of x^row in monomial col.
            M = [[cols[col][row] for col in range(ncols)] for row in range(N)]
            neq = N
            margin = neq - ncols   # over-determination margin (homogeneous: need rank=ncols-1 for 1-dim null)
            rank, basis = nullspace(M, ncols)
            # A nontrivial relation exists iff nullspace dim >= 1.
            # For an over-determined GENUINE relation we want exactly dim 1 typically,
            # and margin (neq - ncols) >= 5 so it's not just under-determined.
            found = False
            poly = None
            if len(basis) >= 1 and margin >= 5:
                # verify each basis vector annihilates all N coefficients (it does by construction
                # within the N rows used); the real test is margin and that the relation is
                # genuinely over-determined. Take the (unique if dim==1) solution.
                iv = to_int_vector(basis[0])
                # double check: residual on all N equations
                ok = True
                for row in range(N):
                    s = Fr(0)
                    for col in range(ncols):
                        s += Fr(iv[col]) * cols[col][row]
                    if s != 0:
                        ok = False
                        break
                if ok:
                    found = True
                    poly = (colinfo, iv)
            results.append((dx, dy, ncols, margin, rank, len(basis), found))
            if found and hit is None:
                hit = (dx, dy, poly)
    return results, hit

# ===========================================================================
# TEST 2: Holonomic / D-finite recurrence
#   sum_{i=0..r} p_i(n) u_{n-i} = 0,   deg p_i <= d
#   p_i(n) = sum_{e=0..d} a_{i,e} n^e
# Unknowns: (r+1)(d+1).  Equations: one per valid n (n from r .. N-1).
# ===========================================================================
def test_holonomic():
    results = []
    hit = None
    Ufr = [Fr(v) for v in U]
    for r in range(1, 9):                 # order
        for d in range(0, 9):             # degree of polynomial coeffs
            unknowns = (r + 1) * (d + 1)
            if unknowns > 32:
                continue
            # equations for n = r .. N-1
            ns = list(range(r, N))
            neq = len(ns)
            margin = neq - unknowns
            if neq < unknowns + 1:
                results.append((r, d, unknowns, neq, margin, None, False, "too few eqs"))
                continue
            # Build matrix: row per n, col per (i,e): value = n^e * u_{n-i}
            M = []
            for n in ns:
                row = []
                for i in range(r + 1):
                    un = Ufr[n - i]
                    for e in range(d + 1):
                        row.append(Fr(n) ** e * un)
                M.append(row)
            rank, basis = nullspace(M, unknowns)
            found = False
            if len(basis) >= 1 and margin >= 5:
                iv = to_int_vector(basis[0])
                # verify residual over all equations
                ok = True
                for ri, n in enumerate(ns):
                    s = Fr(0)
                    idx = 0
                    for i in range(r + 1):
                        un = Ufr[n - i]
                        for e in range(d + 1):
                            s += Fr(iv[idx]) * (Fr(n) ** e) * un
                            idx += 1
                    if s != 0:
                        ok = False
                        break
                if ok:
                    found = True
            results.append((r, d, unknowns, neq, margin, rank, found, ""))
            if found and hit is None:
                hit = (r, d, to_int_vector(basis[0]))
    return results, hit

# ===========================================================================
# TEST 3: Constant-coefficient linear recurrence
#   u_n = sum_{i=1..L} c_i u_{n-i}
# Equations: n = L .. N-1  ->  neq = N - L.  Unknowns: L.
# Need neq > L for over-determination. Report largest L ruled out.
# ===========================================================================
def test_const_rec():
    results = []
    Ufr = [Fr(v) for v in U]
    largest_ruled_out = 0
    hit = None
    for L in range(1, 22):
        ns = list(range(L, N))
        neq = len(ns)
        unknowns = L
        margin = neq - unknowns
        if neq < unknowns + 1:
            results.append((L, neq, margin, None, "too few eqs"))
            continue
        # Solve least-squares-free: set up homogeneous system
        #   u_n - sum c_i u_{n-i} = 0
        # Treat as: find c solving the (neq x L) system exactly; check consistency.
        # Build A (neq x L) and b (neq).  A[k][i-1] = u_{n-i}, b[k] = u_n.
        A = []
        b = []
        for n in ns:
            A.append([Ufr[n - i] for i in range(1, L + 1)])
            b.append(Ufr[n])
        # Solve via exact Gaussian elimination on augmented [A | b]; check the
        # over-determined system is consistent.
        aug = [A[k][:] + [b[k]] for k in range(neq)]
        # forward eliminate
        M = [row[:] for row in aug]
        nrows = neq
        ncols = L + 1
        pivot_cols = []
        rr = 0
        for c in range(L):  # only pivot on the L coefficient columns
            piv = None
            for i in range(rr, nrows):
                if M[i][c] != 0:
                    piv = i
                    break
            if piv is None:
                continue
            M[rr], M[piv] = M[piv], M[rr]
            pv = M[rr][c]
            M[rr] = [x / pv for x in M[rr]]
            for i in range(nrows):
                if i != rr and M[i][c] != 0:
                    f = M[i][c]
                    M[i] = [a - f * bb for a, bb in zip(M[i], M[rr])]
            pivot_cols.append(c)
            rr += 1
            if rr == nrows:
                break
        # After elimination, consistency requires every row with all-zero A-part
        # to also have zero b-part.
        consistent = True
        for i in range(nrows):
            apart = M[i][:L]
            bpart = M[i][L]
            if all(x == 0 for x in apart) and bpart != 0:
                consistent = False
                break
        rank_A = len(pivot_cols)
        # A genuine recurrence of order exactly L: consistent AND rank_A == L
        # (unique solution) AND margin>=5 over-determination.
        found = consistent and (rank_A == L) and (margin >= 5)
        if found and hit is None:
            # recover solution
            sol = [Fr(0)] * L
            for i, c in enumerate(pivot_cols):
                sol[c] = M[i][L]
            hit = (L, sol)
        if not found:
            largest_ruled_out = max(largest_ruled_out, L) if (margin >= 1) else largest_ruled_out
        results.append((L, neq, margin, found, "consistent" if consistent else "INCONSISTENT(ruled out)"))
    return results, hit, largest_ruled_out

# ===========================================================================
if __name__ == "__main__":
    print("=" * 78)
    print("TEST 1 : ALGEBRAIC  P(x,F)=0   (dy in 2..6, dx in 2..14, unknowns<=36)")
    print("=" * 78)
    r1, hit1 = test_algebraic()
    print(f"{'dx':>3} {'dy':>3} {'#unk':>5} {'margin':>7} {'rank':>5} {'nulldim':>8} {'HIT':>5}")
    for (dx, dy, nc, margin, rank, nd, found) in r1:
        print(f"{dx:>3} {dy:>3} {nc:>5} {margin:>7} {rank:>5} {nd:>8} {str(found):>5}")
    if hit1:
        print("\n*** ALGEBRAIC HIT ***")
        dx, dy, (colinfo, iv) = hit1
        print(f"smallest (dx,dy) = ({dx},{dy})")
        terms = []
        for (i, j), c in zip(colinfo, iv):
            if c != 0:
                terms.append(f"({c})*x^{i}*F^{j}")
        print("  " + " + ".join(terms) + " = 0")
    else:
        print("\nALGEBRAIC: none over the whole grid.")

    print()
    print("=" * 78)
    print("TEST 2 : HOLONOMIC / D-finite  (order r 1..8, deg d 0..8, unknowns<=32)")
    print("=" * 78)
    r2, hit2 = test_holonomic()
    print(f"{'r':>3} {'d':>3} {'#unk':>5} {'#eq':>5} {'margin':>7} {'rank':>5} {'HIT':>5} note")
    for row in r2:
        r, d, unk, neq, margin, rank, found, note = row
        print(f"{r:>3} {d:>3} {unk:>5} {neq:>5} {margin:>7} {str(rank):>5} {str(found):>5} {note}")
    if hit2:
        print("\n*** HOLONOMIC HIT ***", hit2[:2])
    else:
        print("\nHOLONOMIC: none over the whole grid.")

    print()
    print("=" * 78)
    print("TEST 3 : CONST-COEFF LINEAR RECURRENCE (order L 1..21)")
    print("=" * 78)
    r3, hit3, lro = test_const_rec()
    print(f"{'L':>3} {'#eq':>5} {'margin':>7} {'HIT':>6}  status")
    for row in r3:
        L, neq, margin, found, status = row
        print(f"{L:>3} {neq:>5} {margin:>7} {str(found):>6}  {status}")
    if hit3:
        print("\n*** CONST-REC HIT ***", hit3)
    else:
        print(f"\nCONST-REC: none. Largest order ruled out (with margin>=1): L={lro}")
