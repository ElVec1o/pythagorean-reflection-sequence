import mpmath as mp
mp.mp.dps=50
exec(open('struct_probe.py').read().split('# The forward')[0])

# Continuum theory. Homog recursion: L_{b+1}-(1+q)L_b+qL_{b-1}=2(1-q)q^{2b+1}L_b.
# Write tau=-ln q. q=e^{-tau}. Let psi_b = q^{-b/2} L_b (remove the q^b mode's sqrt drift).
# Then L_b=q^{b/2}psi_b. Plug in:
#  q^{(b+1)/2}psi_{b+1} - (1+q)q^{b/2}psi_b + q*q^{(b-1)/2}psi_{b-1} = 2(1-q)q^{2b+1}q^{b/2}psi_b
# divide q^{b/2}:
#  q^{1/2}psi_{b+1} - (1+q)psi_b + q^{1/2}psi_{b-1} = 2(1-q)q^{2b+1}psi_b
#  q^{1/2}(psi_{b+1}+psi_{b-1}) - (1+q)psi_b = 2(1-q)q^{2b+1}psi_b
# i.e. psi_{b+1}+psi_{b-1}-2psi_b = [ (1+q)/q^{1/2} - 2 ]psi_b + 2(1-q)q^{2b+1-1/2}psi_b
#  (1+q)/sqrt(q)-2 = (1-sqrt q)^2/sqrt q = (e^{-tau/2}... ) ~ tau^2/4 (since 1-sqrt q~tau/2)
# So discrete 2nd difference psi'' ~ [tau^2/4]psi + 2(1-q)q^{2b+1/2}psi.
# (1-q)~tau, q^{2b}=e^{-2tau b}=u^2 with u=q^b=e^{-tau b}. So RHS2~2tau u^2 psi.
# Let x continuous = tau b? No-- u=e^{-tau b}. d/db. The variable making it Bessel: let
# z = w u = w q^b, w=sqrt(2/tau). Then second-difference in b of psi ~ tau^2 b'' ...
# Standard result: psi_b ~ J0(z)*const + Y0(z)*const, z=w q^b. Let's TEST:
for qf in ['0.97','0.99','0.997']:
    q=mp.mpf(qf); N=int(50/(1-q)); b0,b1,t0,t1,L0,L1=raw(q,N)
    L=[mp.mpf(0)]+L0
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    psi=[L[b]*q**(-mp.mpf(b)/2) for b in range(N)]
    # fit psi_b = a*J0(w q^b)+c*Y0(w q^b) using two b points, test others
    def basis(b):
        z=w*q**b
        return mp.besselj(0,z), mp.bessely(0,z)
    import numpy as np
    b1i,b2i=2,5
    J1,Y1=basis(b1i); J2,Y2=basis(b2i)
    M=mp.matrix([[J1,Y1],[J2,Y2]]); rhs=mp.matrix([psi[b1i],psi[b2i]])
    sol=mp.lu_solve(M,rhs); a,c=sol[0],sol[1]
    print(f'\nq={qf} w={float(w):.3f} a={float(a):.4f} c={float(c):.4f}')
    for b in [1,3,8,16,30]:
        if b>=N: continue
        J,Y=basis(b); pred=a*J+c*Y
        print(f'  b={b:>3} psi={float(psi[b]):>10.4f} pred={float(pred):>10.4f} rel={float((pred-psi[b])/(abs(psi[b])+1e-9)):.4f}')
