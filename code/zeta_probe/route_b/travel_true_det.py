#!/usr/bin/env python3
"""
Build the connectivity-aware TRUE travel transfer matrix M_C(x) (component-multiset
states, isolated cycles pruned in the interior) and study det(I - M_C(x)):
  - its smallest positive real root r_C (in x); compare r_C^2 to q* = 0.449453631
    (the relaxed travel pole). If r_C^2 -> q*, the TRUE travel block has the SAME
    dominant singularity (confirming R1 / Prop travelinv at the operator level).
  - Whether the relaxed travel resolvent's denominator 1-Sigma_1 EQUALS det(I-M_C)
    in the limit (the connectivity constraint does not change the travel denominator).

We evaluate det(I - M_C(x)) numerically at x in (0,1) and locate sign changes.
"""
import sys, os, importlib.util
import mpmath as mp
mp.mp.dps=30

HERE=os.path.dirname(os.path.abspath(__file__))
spec=importlib.util.spec_from_file_location("ttt", os.path.join(HERE,"travel_true_transfer.py"))
ttt=importlib.util.module_from_spec(spec)
_sv=list(sys.argv); sys.argv=["ttt"];
import sympy as sp
spec.loader.exec_module(ttt); sys.argv=_sv

def det_I_minus_M(MC, MS, xval):
    states=ttt.build_states(MC, MS)
    n=len(states)
    idx={s:i for i,s in enumerate(states)}
    # build numeric matrix I - M at x=xval
    M=mp.zeros(n,n)
    for s in states:
        for (ns,xp) in ttt.append_edge(s,1,MS):
            if ns in idx:
                M[idx[ns],idx[s]] += mp.mpf(xval)**xp
    I=mp.eye(n)
    return mp.det(I-M), n

# relaxed travel Sigma_1 for comparison
def Aq(k,q): return 2*q/(1-q**(k+1))
def Cq(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sig_t(k,q,J=4000):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=Aq(k+2*j,q)*prod; prod*=Cq(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-40) and j>40: break
    return tot

if __name__=="__main__":
    MS=int(sys.argv[1]) if len(sys.argv)>1 else 7
    qstar=mp.mpf('0.449453630558948')
    xstar=mp.sqrt(qstar)
    print(f"q* = {mp.nstr(qstar,12)}  x* = {mp.nstr(xstar,12)}")
    print(f"relaxed: 1 - Sigma_1(q*) = {mp.nstr(1-Sig_t(1,qstar),8)} (=0 at the travel pole)")
    print()
    for MC in (1,2,3):
        # scan x for smallest root of det(I-M_C)
        prev=None; root=None; pq=None
        x=mp.mpf('0.3')
        try:
            while x<mp.mpf('0.95'):
                d,n=det_I_minus_M(MC,MS,x)
                if prev is not None and prev*d<0:
                    root=(pq+x)/2; break
                prev=d; pq=x; x+=mp.mpf('0.01')
            print(f"MC={MC}: #states={n}, smallest det(I-M) sign-change at x~{mp.nstr(root,8) if root else 'none<0.95'}  -> x^2~{mp.nstr(root**2,8) if root else '-'}")
        except Exception as e:
            print(f"MC={MC}: error {e}")
    print("\nIf x_root^2 -> q*=0.44945, the TRUE travel transfer shares the relaxed travel pole.")
