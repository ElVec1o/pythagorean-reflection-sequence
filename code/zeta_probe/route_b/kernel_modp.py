#!/usr/bin/env python3
"""
Orthogonal route, deep tool: compute (u_n mod p) for n=0..N via the VALIDATED polynomial-time
catalytic engine true_gf.py, then test (u_n mod p) for p-automaticity (the p-kernel).

WHY THIS IS CORRECT (not a re-port): we import true_gf.slice_gf UNCHANGED and only replace its
inner accumulator `padd` by a mod-p version. The catalytic transfer adds counts and pushes all
costs into EXPONENTS (x-degree, cycle-count), never multiplying coefficients, so reducing every
coefficient mod p is an exact ring homomorphism: u_n mod p is computed exactly. Keeping coeffs in
0..p-1 (small ints) is the speedup over the big-int original. Engine validated against u_0..u_42
(the BFS/OEIS b-file); terms past n=42 are conditional on the closed-form c(g) holding there.

USAGE
  cd code/zeta_probe/route_b
  python3 kernel_modp.py N P [WORKDIR]
    N       : max depth (number of terms u_0..u_N).  k=3 kernel test needs N>=110; k=4 needs N>=250.
    P       : prime (use 3 first -- the promising one; 2 is dead/periodic).
    WORKDIR : checkpoint dir (default ./kmodp_work).  Resumable + atomic save; safe to Ctrl-C/reboot.
  e.g.  python3 kernel_modp.py 120 3
Progress + ETA printed per k.  Writes u_mod{P}_N{N}.txt and prints the automaticity verdict.
Re-run analysis only (fast):  python3 kernel_modp.py analyze u_mod3_N120.txt 3
"""
import sys, os, time, pickle
from collections import defaultdict

# ---------- analysis-only fast path ----------
def analyze(seq, p, kmax=5):
    N=len(seq)-1
    print(f"# analyzing {len(seq)} terms (u_0..u_{N}) mod {p}")
    # eventual periodicity -- ROBUST: preperiod <= L/2 AND >= MINREP full periods of evidence
    # (avoids the spurious "period-2 over the last 4 terms" tail artifact)
    L=len(seq); ep=None; MINREP=5
    for Pr in range(1, L//(MINREP+1)+1):
        for t in range(0, min(L//2, L-MINREP*Pr)+1):
            if all(seq[i]==seq[i+Pr] for i in range(t, L-Pr)):
                ep=(t,Pr); break
        if ep: break
    if ep: print(f"  EVENTUALLY PERIODIC: preperiod {ep[0]}, period {ep[1]} => U mod {p} RATIONAL => automatic => ROUTE DEAD for p={p}")
    else:  print(f"  NOT eventually periodic (no period<= {L//2})")
    # p-kernel: e_{k,r}(n)=seq[p^k n + r]; dedup by agreement on common domain (require overlap>=MINOV)
    MINOV=4
    elems=[]; per_level=[]
    for k in range(0,kmax+1):
        pk=p**k; new=0; reliable=True
        for r in range(pk):
            sub=tuple(seq[pk*n+r] for n in range((N-r)//pk+1) if pk*n+r<=N)
            if len(sub)<MINOV:
                reliable=False; continue
            dup=False
            for e in elems:
                m=min(len(e),len(sub))
                if m>=MINOV and e[:m]==sub[:m]: dup=True; break
            if not dup: elems.append(sub); new+=1
        per_level.append((k,new,len(elems),reliable))
        flag="" if reliable else "  <-- subsequences too short here; need more terms"
        print(f"  k={k}: +{new} new, cumulative distinct kernel elements = {len(elems)}{flag}")
    grow=[per_level[i][2] for i in range(len(per_level))]
    print(f"  kernel growth 0..{kmax}: {grow}")
    print("  VERDICT: if the cumulative count keeps RISING at the last RELIABLE k, that is evidence of an")
    print("           INFINITE p-kernel => (u_n mod p) NOT p-automatic => U TRANSCENDENTAL (unconditional).")
    print("           If it PLATEAUS at a reliable k, evidence of automaticity (route weakens for this p).")
    return grow

if len(sys.argv)>=2 and sys.argv[1]=="analyze":
    path=sys.argv[2]; p=int(sys.argv[3])
    seq=[int(x) for x in open(path).read().split()]
    analyze(seq,p); sys.exit(0)

# ---------- heavy compute path ----------
N=int(sys.argv[1]); P=int(sys.argv[2])
WORK=sys.argv[3] if len(sys.argv)>3 else "./kmodp_work"
os.makedirs(WORK, exist_ok=True)
ckpt=os.path.join(WORK, f"ckpt_N{N}_P{P}.pkl")

import true_gf  # validated engine (imports fast_relaxed3, c_formula)
from functools import lru_cache

# Speedup (results-preserving): boundary_site_cost is a PURE function of a small discrete domain
# (aL,fL,aR,fR,is0,isk,eps,delta) but does a nested optimization each call. Memoize it.
true_gf.boundary_site_cost = lru_cache(maxsize=None)(true_gf.boundary_site_cost)
true_gf.deposits          = lru_cache(maxsize=None)(true_gf.deposits)

# mod-p accumulator AND 1-D collapse (exact, results-preserving):
# true_gf keeps a 2-D (relaxed-length d, cycle-count nc) table so it can output BOTH V and U.
# We only want U, and true_len = relaxed_len + 2*nc by definition. So fold the cycle increment
# dc straight into the length (+2*dc) and keep nc identically 0. This collapses an O(N) dimension
# (=> O(N^4) not O(N^5)) and reduces all counts mod P. U_n is read off directly as table[(n,0)].
def modp_padd(tgt, src, dx, dc):
    realdx = dx + 2*dc            # <-- the fold: 2 length-units per isolated cycle
    for d,sub in src.items():
        t=tgt[d+realdx]
        for nc,cnt in sub.items():   # nc is always 0
            v=(t[nc]+cnt)%P
            if v: t[nc]=v
            elif nc in t: del t[nc]
true_gf.padd = modp_padd   # slice_gf now tracks true-length mod P (1-D, small ints => fast)

cap=N//3+2; kmax=N//2+1
ks_all=list(range(-kmax,kmax+1))
table=defaultdict(int); done=set()
if os.path.exists(ckpt):
    st=pickle.load(open(ckpt,'rb')); table=defaultdict(int,st['table']); done=set(st['done'])
    print(f"# resumed from checkpoint: {len(done)}/{len(ks_all)} k-values done")
todo=[k for k in ks_all if k not in done]
print(f"# computing u_n mod {P} for n=0..{N}  ({len(todo)} k-slices remaining, cap={cap})")
t0=time.time()
for i,k in enumerate(todo,1):
    for eps in (1,-1):
        for delta in (0,1):
            gf=true_gf.slice_gf(eps,delta,k,N,cap)
            for d,sub in gf.items():
                if d<=N:
                    for nc,cnt in sub.items():
                        table[(d,nc)]=(table[(d,nc)]+cnt)%P
    done.add(k)
    el=time.time()-t0; eta=el/i*(len(todo)-i)
    print(f"  k={k:+4d}  ({i}/{len(todo)})  elapsed {el:6.0f}s  ETA {eta:6.0f}s  (~{eta/60:.1f}m)  |table|={len(table)}", flush=True)
    pickle.dump({'table':dict(table),'done':list(done)}, open(ckpt+'.tmp','wb'))
    os.replace(ckpt+'.tmp', ckpt)   # atomic

U=[0]*(N+1)
for (Lr,c),cnt in table.items():
    t=Lr+2*c
    if t<=N: U[t]=(U[t]+cnt)%P
# sanity: validate against the 43 known u_n mod P
ref=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,
     62263,94622,143881,217101,327832,495443,749195,1127236,1697179,2554961,3848384,5777651,8679441,
     13031206,19574659,29338781,43997388,65932461,98849591,147969934]
bad=[n for n in range(min(N+1,len(ref))) if U[n]!=ref[n]%P]
print(f"# validation vs 43 known u_n mod {P}: {'OK' if not bad else 'MISMATCH at '+str(bad)}")
out=f"u_mod{P}_N{N}.txt"
open(out,'w').write(" ".join(str(x) for x in U))
print(f"# wrote {out}")
analyze(U, P)
