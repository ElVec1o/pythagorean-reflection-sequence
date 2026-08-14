#!/usr/bin/env python3
"""
Does the ASSEMBLED relaxed V(x)=sum v_n x^n carry the BULK pole family, or only the travel one?
Pade-approximant pole extraction on 131 exact terms (V130.json).
  travel poles (x=sqrt(q_trav)): q=0.4495,0.9135,0.9680,... -> x=0.6704,0.9558,0.9839,...
  bulk   poles (x=sqrt(q_bulk)): q=0.6096,0.9202,0.9690,... -> x=0.7808,0.9593,0.9844,...
If x~0.7808 (bulk dominant) appears as a Pade pole of V, the assembled V genuinely has the
bulk family (=> a second, independent pole source).
"""
import mpmath as mp, json, os
mp.mp.dps=80
HERE=os.path.dirname(os.path.abspath(__file__))
c=[mp.mpf(s) for s in json.load(open(os.path.join(HERE,'V130.json')))]
N=len(c); print(f"loaded {N} terms of V(x)")

def pade_poles(c, M):
    L=len(c)-M-1
    # solve sum_{j=1..M} b_j c_{L+i-j} = -c_{L+i}, i=1..M
    A=mp.matrix(M,M); rhs=mp.matrix(M,1)
    for i in range(1,M+1):
        for j in range(1,M+1):
            idx=L+i-j
            A[i-1,j-1]=c[idx] if 0<=idx<len(c) else mp.mpf(0)
        rhs[i-1,0]=-c[L+i]
    b=mp.lu_solve(A,rhs)
    bden=[mp.mpf(1)]+[b[k,0] for k in range(M)]   # B(x)=sum bden[j] x^j
    roots=mp.polyroots(list(reversed(bden)), maxsteps=2000, extraprec=400)
    return roots

# reference pole locations in x
trav_q=[0.449535,0.913487,0.968042,0.983579,0.990037,0.993321]
bulk_q=[0.609567,0.920165,0.969020,0.983843,0.990135,0.993365]
trav_x=[mp.sqrt(mp.mpf(q)) for q in trav_q]
bulk_x=[mp.sqrt(mp.mpf(q)) for q in bulk_q]

for M in [45,55,62]:
    print(f"\n===== Pade [.../{M}] =====")
    roots=pade_poles(c,M)
    real_in=[r.real for r in roots if abs(r.imag)<mp.mpf(10)**(-6) and 0<r.real<1.02]
    real_in=sorted(set(round(float(r),5) for r in real_in))
    print("real poles in (0,1.02):", real_in[:25])
    # classify each near-1 reference
    def nearest(x, pset):
        ds=[(abs(p-mp.mpf(x)),float(p)) for p in pset]
        return min(ds)
    print(f"{'target':>10} {'family':>7} {'matched?':>10} {'dist':>10}")
    for q,x in zip(trav_q,trav_x):
        d,p=min([(abs(mp.mpf(rp)-x),rp) for rp in real_in]) if real_in else (mp.mpf(9),0)
        print(f"{float(x):>10.5f} {'travel':>7} {p if d<2e-3 else '  --':>10} {float(d):>10.2e}")
    for q,x in zip(bulk_q,bulk_x):
        d,p=min([(abs(mp.mpf(rp)-x),rp) for rp in real_in]) if real_in else (mp.mpf(9),0)
        print(f"{float(x):>10.5f} {'BULK':>7} {p if d<2e-3 else '  --':>10} {float(d):>10.2e}")
