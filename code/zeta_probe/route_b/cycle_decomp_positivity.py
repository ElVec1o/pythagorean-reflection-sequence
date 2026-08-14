#!/usr/bin/env python3
"""
NEW ANGLE for U: cycle-count positivity.
  N_U(q) = sum_c q^c B_c(q),   N_V(q) = sum_c B_c(q) = S_0  (relaxed numerator, y-free).
  B_c = bulk numerator restricted to exactly c isolated cycles (relaxed-length graded, >=0 coeffs).
If all B_c(q_m) share sign at a travel pole q_m, then N_U(q_m)=sum_c q_m^c B_c(q_m) is a sum of
same-sign terms (weights q_m^c in (0,1]) => NONZERO, and 0<|N_U|<=|N_V|. Unlike the junction
decomposition (mixed signs, dead), the CYCLE decomposition has a chance at positivity.

This script:
 (1) Build B_c(q) for c=0..Cmax by bulk enumeration (relaxed length + cycle count c).
 (2) sum_c B_c == S_0 (relaxed bulk numerator) as series  [consistency].
 (3) sign(B_c(q)) coherence on (0, bulk_radius): do all B_c share sign at each q? (the
     ingredient the secondary-pole argument needs, tested where the series converge).
 (4) N_U(q)=sum_c q^c B_c vs N_V=sum_c B_c: ratio in (0,1], and (Pringsheim) at the dominant
     regime all residues same sign.
"""
import sys, os, importlib.util
from collections import defaultdict
import mpmath as mp
mp.mp.dps=40
HERE=os.path.dirname(os.path.abspath(__file__))
import lamp_lib as LL
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf)
relaxed_len=cf.relaxed_len_local

def build_Bc(Nmax_len=24, Smax=4, maxgap=8, maxdep=7):
    """One-sided bulk run anchored at marker0 (eps=1,dl=0,k=0). Resolve by cycle count
       c=(true-relaxed)/2.  B_c[n] += 2^ndep for relaxed length 2n."""
    B=defaultdict(lambda: defaultdict(int))   # B[c][n]
    sizes=[2*m for m in range(1,Smax+1)]
    def rec(a,lastedge,ndep):
        if ndep>=1:
            rl=relaxed_len(1,0,0,a); tl=LL.solve(1,0,0,a)
            if rl is not None and tl is not None and rl<=Nmax_len and rl%2==0:
                c=(tl-rl)//2
                B[c][rl//2]+=2**ndep
        if ndep>=maxdep: return
        for g in range(0,maxgap+1):
            nextedge=lastedge+1+g
            for s in sizes:
                a2=dict(a); a2[nextedge]=s
                if relaxed_len(1,0,0,a2) is None or relaxed_len(1,0,0,a2)>Nmax_len: continue
                rec(a2,nextedge,ndep+1)
    for s in sizes: rec({0:s},0,1)
    return B

print("Building B_c (bulk numerator by cycle count) ...")
B=build_Bc(Nmax_len=22, Smax=4, maxgap=8, maxdep=7)
Cmax=max(B.keys()); NN=12
def Bc_series_val(c,q): return sum(B[c].get(n,0)*q**n for n in range(NN))
print(f"cycle counts present: c=0..{Cmax}")
for c in sorted(B.keys()):
    row=[B[c].get(n,0) for n in range(NN)]
    print(f"  B_{c}: {row}")

# (3) sign coherence of B_c(q) on (0, 0.6) -- all same sign?
print("\nsign(B_c(q)) at sample q (series truncated at n<12; valid for q< bulk radius ~0.61):")
print(f"{'q':>7} " + " ".join(f"B_{c}" for c in sorted(B.keys())) + "   all-same-sign?")
for qf in ['0.2','0.3','0.4','0.5','0.55']:
    q=mp.mpf(qf)
    vals=[Bc_series_val(c,q) for c in sorted(B.keys())]
    signs=[('+' if v>0 else ('-' if v<0 else '0')) for v in vals]
    nz=[s for s in signs if s!='0']
    print(f"{qf:>7} " + "  ".join(signs) + f"     {len(set(nz))<=1}")

# (4) N_U = sum_c q^c B_c  vs  N_V = sum_c B_c, ratio (should be in (0,1], positive)
print("\nN_U/N_V = (sum_c q^c B_c)/(sum_c B_c)  (expect positive, in (0,1]):")
for qf in ['0.2','0.3','0.4','0.5','0.55','0.6']:
    q=mp.mpf(qf)
    NV=sum(Bc_series_val(c,q) for c in sorted(B.keys()))
    NU=sum(q**c*Bc_series_val(c,q) for c in sorted(B.keys()))
    print(f"  q={qf}: N_V={mp.nstr(NV,8)}, N_U={mp.nstr(NU,8)}, ratio={mp.nstr(NU/NV,8)}")
