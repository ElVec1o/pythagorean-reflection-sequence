#!/usr/bin/env python3
"""
Decisive test for SEAM #3: does the cycle marker y enter the BULK DENOMINATOR (move the
cosine poles) or only the numerator?

The relaxed bulk catalytic recursion (validated, reproduces 0,2,2,6,2,18,6,42,18,118,...):
   F_s = 2q^s + 2q^s sum_{s'>=s} F_{s'} q^{s'} + 2q^{2s} sum_{s'<s} F_{s'},  s>=1.

Decompose the coupling. Appending deposit s' to current s:
   s'>=s : site cost max=s' -> factor q^{s'} (SECOND term: this is the magnitude ladder).
   s'<s  : the term carries q^{2s} = q^{max=s} * q^{s}. The EXTRA q^{s} beyond the site cost
           q^{max}=q^s is the REACHABILITY/backtrack slack -- exactly where a forced gap-edge
           (m=2, length 2 -> q) lives when the next deposit is smaller/further. In the TRUE
           metric this backtrack edge is an ISOLATED CYCLE: +2 length -> multiply by y.

So the cycle-marked recursion is:
   F_s = 2q^s + 2q^s sum_{s'>=s} F_{s'} q^{s'} + 2q^{s} (q y)^{?} ...
We mark ONLY the extra-backtrack factor.  Concretely the third term 2q^{2s} = 2 q^{s} * q^{s};
the second q^{s} is the cycle/backtrack -> mark it q^{s} -> (q y? )^{s}? The cycle is a SINGLE
+2 (one edge), independent of magnitude s.  So the correct marking multiplies the third term
by a SINGLE factor y (one cycle per smaller-append backtrack), NOT y^s.

We test THREE markings of the third term and read the denominator poles:
  (a) lam=1 (relaxed): full third term.
  (b) third term * y  (one cycle per smaller-append).
  (c) third term with q^{2s} -> q^s (qy)^s  (cycle per unit, magnitude-dependent -- WRONG per
      validated magnitude-independence, included as a control).
For each, telescope numerically (finite linear solve) and find the denominator zeros.
The DENOMINATOR is where the block GF (I - coupling)^{-1} diverges = spectral radius 1.
We locate poles via det(I - M(q,y)) = 0 on the truncated system and report the family.
"""
import mpmath as mp, sys
mp.mp.dps=24

def block_and_det(q, mode, y, Smax=45):
    sizes=list(range(1,Smax+1)); n=len(sizes); idx={s:i for i,s in enumerate(sizes)}
    M=mp.matrix(n,n); b=mp.matrix(n,1)
    for s in sizes:
        b[idx[s],0]=2*q**s
        for sp in sizes:
            if sp>=s:
                M[idx[s],idx[sp]]+=2*q**s*q**sp
            else:
                # third term base 2 q^{2s}
                if mode=='relaxed':
                    M[idx[s],idx[sp]]+=2*q**(2*s)
                elif mode=='y_single':       # one cycle per smaller-append
                    M[idx[s],idx[sp]]+=2*q**(2*s)*y
                elif mode=='y_persize':       # control: y per unit size
                    M[idx[s],idx[sp]]+=2*q**(s)*(q*y)**s
    A=mp.eye(n)-M
    return mp.det(A)

def fz(f,nmax,wlo=2.0,whi=40,step=0.04):
    roots=[]; prev=None; pq=None; w=mp.mpf(wlo)
    while len(roots)<nmax and w<whi:
        q=mp.e**(-2/w**2)
        try: val=f(q)
        except: val=None
        if val is not None and prev is not None and mp.sign(val)!=mp.sign(prev) and prev!=0:
            try:
                r=mp.findroot(f,(pq+q)/2)
                if 0<r<1 and (not roots or abs(r-roots[-1])>mp.mpf(10)**(-9)): roots.append(r)
            except: pass
        prev=val if val is not None else prev; pq=q; w+=step
    return sorted(roots)

if __name__=="__main__":
    # (a) relaxed: should reproduce 1-S1 family 0.6096,0.9202,0.9690,...
    za=fz(lambda q: block_and_det(q,'relaxed',mp.mpf(1)),6)
    print('relaxed det=0:', [mp.nstr(r,8) for r in za]); sys.stdout.flush()
    # (b) y_single at y=q (TRUE): does the family survive / move?
    zb1=fz(lambda q: block_and_det(q,'y_single',mp.mpf(1)),6)
    print('y_single y=1 :', [mp.nstr(r,8) for r in zb1]); sys.stdout.flush()
    zbq=fz(lambda q: block_and_det(q,'y_single',q) if False else block_and_det(q,'y_single',q),6)
    # y depends on q -> need y inside; recompute with y=q
    def detq(q): return block_and_det(q,'y_single',q)
    zbq=fz(detq,6)
    print('y_single y=q :', [mp.nstr(r,8) for r in zbq]); sys.stdout.flush()
    print('DONE'); sys.stdout.flush()
