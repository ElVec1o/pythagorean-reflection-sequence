"""
D6 SHORTCUT INVESTIGATION -- consolidated findings & verification.
All checks at the travel poles, high precision.

VERDICT:
 * Route (a) ABSOLUTE contour bound on integral rep: PARTIALLY VIABLE but does NOT shortcut.
     The integral rep (fact 6) is for Y3(1/q) (the connection coefficient object). An absolute
     |.| bound gives |Y3(1/q)| but the gate needs the CANCELLATION between pref*Y3 and (2/3)Se
     (both O(sqrt tau)); an absolute bound on Y3 alone cannot see the cancellation -> only gives
     |P12| = O(sqrt tau), TOO WEAK. (lem:T2abs worked for V because V = a RATIO whose numerator
     is bounded; here P12 is a DIFFERENCE of two O(sqrt tau) terms.) DEAD as a standalone shortcut.
 * Route (b) SECOND EXACT IDENTITY via det + unimodularity: REAL & CLEAN, partially shortcuts.
     NEW EXACT IDENTITIES (q-algebraic, no saddle):
       [E1] det P = 1                       (per-step det M_n=1)
       [E2] P11 + P21 = 1 - Sig_t           (verified ratio==1 to 1e-66, ALL q)
       [E3] => at poles (Sig_t=1): P21=-P11 => P11(Se+P12)=1 => P12 = 1/P11 - Se   (EXACT)
     This is a genuine NEW pinning of P12 with NO connection coefficient (no 36/35, no q-Bessel).
     BUT bounding 1/P11 - Se still needs P11's saddle to one order -> reduces to [S2] below.
 * Route (c) RATIONAL t1-series: the rationality is GENUINELY POLE-SPECIFIC (P11*Se oscillates
     off-pole). The cancellation mechanism is: P11 = w sin w R11 (R11 smooth), and the pole
     condition cos w = O(sqrt tau) makes the saddle phase rational. No GF/contiguous-relation
     proof of rationality found; it reduces to the SAME [S2] saddle bound.

ALL THREE routes converge to ONE lem:cos-class subleading bound at the pole phase:
   [S2]   cos(w_m) - T2_Se(q_m) = O(tau^{3/2}),   T2_Se := cos(W_m) - Se(q_m).
   (equivalently T2_Se = T2_travel + O(tau^{3/2}): the Se-side and travel-side saddle corrections
    AGREE to one deeper order at the pole.) Given [S2] + the EXACT identity [E3], the gate is immediate:
       P12 = 1/P11 - Se, and the O(sqrt tau) parts cancel via [S2], leaving |P12| ~ (1/(4 sqrt2)) tau^{3/2}.
   This MATCHES MEMORY's standing assessment: U transcendental <= lem:cos + ONE parallel subleading bound.

NET CONTRIBUTION OF D6: route (b)'s exact identities [E1][E2][E3] REPLACE the entire q-Bessel
connection-coefficient assembly (fact 4/9, the 36/35, the Laplace/stationary-phase of fact 6) with
THREE elementary q-algebraic identities + ONE V-class saddle bound [S2]. The hardest analytic object
(the connection coefficient 36/35 coupling q-Bessel to pole phase) is ELIMINATED. The residual [S2]
is strictly in the V/lem:cos family (no new transcendental constant), one order beyond lem:T2abs.
"""
import mpmath as mp

def cocycle_full(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return X,Y,x,y   # P11,P12,P21,P22(=Se)

def Sig_t(q):
    q=mp.mpf(q); S=mp.mpf(0); pr=mp.mpf(1)
    maxj=int(220/(1-q))+50
    for j in range(maxj):
        k=1+2*j; S+=2*q/(1-q**(k+1))*pr
        pr*=2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10): break
    return S

poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*92)
print("D6 SHORTCUT FINDINGS -- numerical verification")
print("="*92)

# E2: P11+P21 = 1-Sig_t at GENERIC q (the new exact identity)
print("\n[E2] EXACT identity  P11 + P21 = 1 - Sig_t   (holds for ALL q, NOT just poles)")
mp.mp.dps=100
for qf in ['0.90','0.95','0.97','0.99','0.995']:
    q=mp.mpf(qf); N=int(160/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N)
    res=(P11+P21)-(1-Sig_t(q))
    print(f"   q={qf}:  (P11+P21)-(1-Sig_t) = {mp.nstr(res,4)}   [== 0]")

# E1+E3: det=1 and P12 = 1/P11 - Se at poles
print("\n[E1]+[E3] det P = 1 (exact) and  P12 = 1/P11 - Se  at poles")
print(f"   {'m':>3} {'tau':>10} {'det-1':>10} {'P12 - (1/P11 - Se)':>20}")
for m in [4,8,16,32]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=40+int(2.5*float(w)); q=poles[m-1]; tau=-mp.log(q); N=int(95/(1-q))
    P11,P12,P21,P22=cocycle_full(q,N)
    print(f"   {m:>3} {float(tau):>10.3e} {mp.nstr(P11*P22-P12*P21-1,3):>10} {mp.nstr(P12-(1/P11-P22),3):>20}")

# [S2] the lone residual bound, and the gate
print("\n[S2] cos(w) - T2_Se = O(tau^{3/2})  (the lone lem:cos-class subleading bound)  &  GATE")
print(f"   {'m':>3} {'tau':>10} {'(cosw-T2_Se)/t^1.5':>18} {'|P12|/t^1.5':>12} {'gate 1/sqrt2':>12}")
sup=mp.mpf(0)
for m in [4,8,16,24,32,40,50,60]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=60+int(3.0*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(95/(1-q)); W=w*mp.exp(-tau/2)
    P11,P12,P21,P22=cocycle_full(q,N)
    T2=mp.cos(W)-P22; cmt=mp.cos(w)-T2
    r=abs(P12)/tau**mp.mpf('1.5')
    if r>sup: sup=r
    print(f"   {m:>3} {float(tau):>10.3e} {float(cmt/tau**mp.mpf('1.5')):>18.7f} {float(r):>12.7f} {float(1/mp.sqrt(2)):>12.7f}")
    mp.mp.dps=50
print(f"\n   sup |P12|/tau^{{3/2}} = {float(sup):.6f}  <<  1/sqrt2 = {float(1/mp.sqrt(2)):.6f}  (4x margin)")
print(f"   leading const 1/(4 sqrt2) = {float(1/(4*mp.sqrt(2))):.6f}  =  A_lead(0.3246) + B_lead(-0.1478)")

print("\n"+"="*92)
print("CONCLUSION: route (b) exact identities ELIMINATE the q-Bessel connection coefficient.")
print("Gate <=> [S2] (one V-class saddle bound, one order beyond lem:T2abs, at the pole phase).")
print("="*92)
