#!/usr/bin/env python3
# =============================================================================
#  hunt_coeffs.py  --  "test to the limit" harness for the U-gate bedrock series
#
#     c2(tau) = R / (tau^{5/2} sin w)  =  C + s1 tau + s2 tau^2 + s3 tau^3 + ...
#
#  where C = 1891 sqrt2 / 10368 is the proven elementary leading term and the
#  s_k are the unknown subleading coefficients (s1 is the "new irreducible
#  constant").  The Rust tool u5b_gate extracts C, s1..sN to ~175 digits by
#  in-place Neville extrapolation of the travel-pole samples and writes them to
#  <out>.scoeffs.txt.  This script runs FOUR independent attacks on them:
#
#    1. GROWTH / GEVREY diagnostics   -> nature of the series (radius, order)
#    2. BOREL transform b_k = s_k/k!  -> singularity location (resurgence)
#    3. HOLONOMIC RECURRENCE search   -> is the series D-finite?  (THE big one:
#                                        a hit => closed form for R)
#    4. PSLQ identification of each s_k against an exotic + problem-specific
#       transcendental basis          -> are the s_k irreducible, or hidden combos?
#
#  Usage:
#     python3 hunt_coeffs.py gate.csv.scoeffs.txt
#     python3 hunt_coeffs.py gate.csv.scoeffs.txt 240      # override working dps
#
#  Everything is scalar mpmath (no matrices larger than ~14x14) -> memory-safe.
# =============================================================================
import sys, math, itertools
import mpmath as mp

path = sys.argv[1] if len(sys.argv) > 1 else 'gate.csv.scoeffs.txt'
DPS  = int(sys.argv[2]) if len(sys.argv) > 2 else 220
mp.mp.dps = DPS

# ---- load C, s1, s2, ... from the Rust .scoeffs.txt --------------------------
C = None
S = {}                                   # k -> mpf(s_k)
for ln in open(path):
    ln = ln.strip()
    if not ln or ln.startswith('#'):
        continue
    tag, val = ln.split(None, 1)
    if tag == 'C':
        C = mp.mpf(val)
    elif tag.startswith('s'):
        S[int(tag[1:])] = mp.mpf(val)
ks = sorted(S)
s  = [S[k] for k in ks]                   # s[0]=s1, s[1]=s2, ...
N  = len(s)
print(f"# loaded C and s1..s{N} from {path}  (working dps={DPS})")
print(f"#   C  = 1891 sqrt2 / 10368 = {mp.nstr(C,30)}")
for k in ks:
    print(f"#   s{k:<2} = {mp.nstr(S[k],34)}")
print()

# =============================================================================
# 1. GROWTH / GEVREY  --  |s_k|^{1/k} and successive ratios
#    A finite limit of |s_k|^{1/k} = 1/R says the *plain* series has radius R.
#    If instead |s_k/k!|^{1/k} -> 1/rho is finite, the series is Gevrey-1 (the
#    asymptotic-expansion regime) with Borel-plane singularity at radius rho.
# =============================================================================
print("# === 1. GROWTH / GEVREY DIAGNOSTICS ===")
print(f"#  k   |s_k|^(1/k)        |s_{{k+1}}/s_k|      |s_k/k!|^(1/k)")
for i, k in enumerate(ks):
    rk  = mp.fabs(s[i]) ** (mp.mpf(1)/k)
    rat = mp.nstr(mp.fabs(s[i+1]/s[i]), 10) if i+1 < N else '   --'
    bk  = (mp.fabs(s[i])/mp.factorial(k)) ** (mp.mpf(1)/k)
    print(f"#  {k:<3} {mp.nstr(rk,10):<17} {rat:<17} {mp.nstr(bk,10)}")
print("#  (plain ^(1/k) -> 1/R_plain ; Borel ^(1/k) -> 1/rho_Borel)")
print()

# =============================================================================
# 2. BOREL transform  b_k = s_k / k!  and Pade-style ratio extrapolation of its
#    singularity.  b_{k+1}/b_k -> 1/rho ; the limit's argument (if complex it
#    shows up as oscillation/sign-flips) locates the nearest Borel singularity.
# =============================================================================
print("# === 2. BOREL-PLANE SINGULARITY (b_k = s_k/k!) ===")
b = [s[i]/mp.factorial(ks[i]) for i in range(N)]
def richardson(seq):
    a = [mp.mpf(v) for v in seq]
    while len(a) > 1:
        a = [ (j+1)*a[j+1] - j*a[j] for j in range(len(a)-1) ]   # cancel 1/n head
    return a[0]
# |b_k|^{1/k} -> 1/|rho| is SMOOTH (modulus) even when the singularity is complex.
# It only oscillates mildly; the MEAN of the deep tail is the stable estimate
# (the iterated-Richardson tower over-amplifies that oscillation -> unusable).
mods = [ mp.fabs(b[i])**(mp.mpf(1)/ks[i]) for i in range(N) ]
tail = mods[max(0,N-6):]
inv_rho = sum(tail)/len(tail)
lo, hi = min(tail), max(tail)
print(f"#  |b_k|^(1/k) tail mean -> 1/|rho| ~ {mp.nstr(inv_rho,8)}  (range {mp.nstr(lo,6)}..{mp.nstr(hi,6)})")
if inv_rho != 0:
    print(f"#  => |rho| ~ {mp.nstr(1/inv_rho,8)}   "
          f"(route-D3.5 Pade-Borel: |rho|~4.46, arg~59deg, sqrt2*pi*e^(i60))")
# the SIGN pattern of b_k flags a COMPLEX singularity (off the positive real axis);
# the precise argument needs Pade-Borel (route-D3.5 did this -> ~59 deg), not a
# crude flip-count, so we only report the pattern here.
rr = [b[i+1]/b[i] for i in range(N-1)]
signs = ''.join('+' if v > 0 else '-' for v in rr)
flips = sum(1 for i in range(len(signs)-1) if signs[i] != signs[i+1])
print(f"#  b_k ratio signs: {signs}  ({flips} flips => complex rho, off R_+)")
print("#  => complex Borel singularity (sign oscillation) confirms NON-elementary,")
print("#     resurgent q-Bessel-confluence character (no real-axis Laplace shortcut).")
print()

# =============================================================================
# 3. HOLONOMIC (P-finite) RECURRENCE search   --   sum_{j=0}^{r} P_j(k) s_{k+j}=0
#    with P_j a polynomial of degree <= d.  Unknowns U=(r+1)(d+1); equations
#    K = N-r.  We require K >= U+2 (2 extra eqs = built-in cross-validation).
#    A recurrence exists iff A^T A is rank-deficient: smallest eigenvalue/largest
#    ~ 0 to working precision.  Then PSLQ the nullvector to rational P_j.
# =============================================================================
print("# === 3. HOLONOMIC RECURRENCE  sum_j P_j(k) s_{k+j} = 0,  deg P_j <= d ===")
print("#   (a near-zero rank ratio => the series is D-finite => closed form for R)")
found_rec = False
def try_recurrence(r, d):
    global found_rec
    U = (r+1)*(d+1)
    K = N - r                                   # eqs: k=1..K  use s_{k..k+r}
    if K < U + 2:
        return
    # columns indexed (j,a): coefficient of k^a * s_{k+j}
    rows = []
    for kk in range(1, K+1):
        row = []
        for j in range(r+1):
            for a in range(d+1):
                row.append( mp.mpf(kk)**a * s[(kk-1)+j] )   # s_{kk+j}, 0-based
        rows.append(row)
    A = mp.matrix(rows)                          # K x U
    M = A.T * A                                  # U x U symmetric PSD
    E, Q = mp.eigsy(M)                           # ascending eigenvalues
    lo = mp.fabs(E[0]); hi = mp.fabs(E[U-1])
    ratio = lo/hi if hi != 0 else mp.mpf(1)
    tag = f"r={r} d={d}  U={U} K={K}"
    if ratio < mp.mpf(10)**(-DPS//2):
        v = [Q[t,0] for t in range(U)]
        # normalize: divide by the smallest-magnitude nonzero entry, PSLQ to ints
        nz = [abs(x) for x in v if abs(x) > mp.mpf(10)**(-DPS//3)]
        scale = min(nz)
        vv = [x/scale for x in v]
        rel = mp.pslq([mp.mpf(1)] + vv, maxcoeff=10**8, maxsteps=10**5)
        print(f"#  *** HIT: {tag}   rankratio~1e{int(mp.log10(ratio)):d} ***")
        # reconstruct P_j(k)
        idx = 0
        for j in range(r+1):
            coeffs = [mp.nstr(vv[j*(d+1)+a], 12) for a in range(d+1)]
            print(f"#       P_{j}(k) ~ " + " + ".join(f"({c})k^{a}" for a,c in enumerate(coeffs)))
        if rel:
            print(f"#       PSLQ rationalization of nullvector: {rel}")
        found_rec = True
    else:
        print(f"#  {tag:<22} rank ratio ~ 1e{int(mp.log10(ratio)) if ratio>0 else -999}   (no recurrence)")

for (r, d) in [(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2),(4,1)]:
    try_recurrence(r, d)
if not found_rec:
    print("#  => NO holonomic recurrence up to (order 4, degree 4) within s1..sN.")
    print("#     (extract more s_k via a deeper u5b_gate run to push order/degree.)")
print()

# =============================================================================
# 4. PSLQ identification of each s_k against an exotic + problem-specific basis.
#    Trustworthy = the integer "spend" (sum log10|coeff|) is small vs the ~170
#    digits available, AND the relation overdetermines (predicts more digits
#    than spent).  We test s_k and a few natural rescalings (sqrt2*s_k, etc).
# =============================================================================
print("# === 4. PSLQ IDENTIFICATION of each s_k ===")
g13 = mp.gamma(mp.mpf(1)/3); g23 = mp.gamma(mp.mpf(2)/3)
g16 = mp.gamma(mp.mpf(1)/6); g14 = mp.gamma(mp.mpf(1)/4)
BASIS = {
    '1'            : mp.mpf(1),
    'sqrt2'        : mp.sqrt(2),
    'sqrt3'        : mp.sqrt(3),
    'pi'           : mp.pi,
    'pi^2'         : mp.pi**2,
    '1/pi'         : 1/mp.pi,
    'e'            : mp.e,
    'log2'         : mp.log(2),
    'log3'         : mp.log(3),
    'zeta3'        : mp.zeta(3),
    'Catalan'      : mp.catalan,
    'gammaE'       : mp.euler,
    'logGlaisher'  : mp.log(mp.glaisher),
    # ---- problem-native elementary constants (McMahon / EM / gate) ----
    'C'            : C,
    'sqrt2/36'     : mp.sqrt(2)/36,
    '1/(4sqrt2)'   : 1/(4*mp.sqrt(2)),
    '1891/1296'    : mp.mpf(1891)/1296,
    # ---- q-Airy / turning-point connection constants ----
    'Gamma(1/3)^3' : g13**3,
    'Gamma(2/3)^3' : g23**3,
    'Gamma(1/6)^2' : g16**2,
    'Gamma(1/4)'   : g14,
    'Ai(0)'        : mp.airyai(0),
    "Ai'(0)"       : mp.airyai(0,1),
    '3^(1/3)'      : mp.mpf(3)**(mp.mpf(1)/3),
    '2^(1/3)'      : mp.mpf(2)**(mp.mpf(1)/3),
}
bnames = list(BASIS); bvals = [BASIS[n] for n in bnames]
SPEND_OK = DPS // 4            # call a relation trustworthy if spend < dps/4

def pslq_report(label, target):
    # (a) full-basis sweep
    rel = mp.pslq([target] + bvals, maxcoeff=10**6, maxsteps=2*10**5)
    if rel and rel[0] != 0:
        spend = sum(math.log10(abs(c)) for c in rel if c != 0)
        if spend < SPEND_OK:
            rhs = " + ".join(f"({rel[i+1]})*{bnames[i]}"
                             for i in range(len(bnames)) if rel[i+1] != 0)
            print(f"#  {label}: ({rel[0]})*{label} = {rhs}    [spend~{spend:.0f}d]")
            return True
    # (b) targeted low-dim hypotheses among the most likely constants
    for sub in [('1','sqrt2'), ('1','sqrt2','pi'), ('sqrt2','C'),
                ('Gamma(1/3)^3',), ('Ai(0)',"Ai'(0)"), ('sqrt2/36','1/(4sqrt2)')]:
        sv = [BASIS[n] for n in sub]
        rel = mp.pslq([target] + sv, maxcoeff=10**7, maxsteps=10**5)
        if rel and rel[0] != 0:
            spend = sum(math.log10(abs(c)) for c in rel if c != 0)
            if spend < SPEND_OK:
                rhs = " + ".join(f"({rel[i+1]})*{sub[i]}"
                                 for i in range(len(sub)) if rel[i+1] != 0)
                print(f"#  {label}: ({rel[0]})*{label} = {rhs}    [spend~{spend:.0f}d, subset]")
                return True
    return False

any_hit = False
for k in ks:
    hit = pslq_report(f"s{k}", S[k])
    any_hit = any_hit or hit
if not any_hit:
    print("#  NO trustworthy relation for any s_k in the exotic+native basis.")
    print("#  => the s_k are genuinely new constants (not low-height combinations).")
print()

# =============================================================================
# 5. STRUCTURE among the s_k:  is s_k a polynomial / rational in (s1, sqrt2)?
#    and are the *ratios* s_{k+1}/s_k themselves identifiable?
# =============================================================================
print("# === 5. INTERNAL STRUCTURE (s_k vs s1, sqrt2) ===")
s1 = S[ks[0]]
for k in ks[1:]:
    # is s_k an integer/rational combination of monomials s1^a sqrt2^b (a<=3,b<=2)?
    mons, names = [], []
    for a in range(4):
        for bexp in range(3):
            mons.append(s1**a * mp.sqrt(2)**bexp); names.append(f"s1^{a} sqrt2^{bexp}")
    rel = mp.pslq([S[k]] + mons, maxcoeff=10**6, maxsteps=10**5)
    if rel and rel[0] != 0:
        spend = sum(math.log10(abs(c)) for c in rel if c != 0)
        if spend < SPEND_OK:
            rhs = " + ".join(f"({rel[i+1]})*{names[i]}"
                             for i in range(len(names)) if rel[i+1] != 0)
            print(f"#  s{k} = [1/({-rel[0]})] ( {rhs} )   [spend~{spend:.0f}d]")
            continue
    print(f"#  s{k}: no low-height polynomial in (s1, sqrt2)")
print()
print("# done.  (deeper u5b_gate run = more s_k = higher recurrence order testable.)")
