from mpmath import mp, mpf, mpc, exp, log, pi, sqrt, polylog, nstr, re, im, atan
mp.dps=30
w0=-2*(1-1j); Lw=log(w0)
Phi=lambda x: x*Lw-x*x+(pi**2/6-polylog(2,exp(-8*x)))/16
z=sqrt(1j*(4-sqrt(15)))   # principal root
for zz in (z,-z):
    xs=-log(zz)/2
    dPhi=Lw-2*xs-log(1-exp(-8*xs))/2
    print('z=',nstr(zz,8),' xs=',nstr(xs,8),' Phi_i\'(xs)=',nstr(dPhi,5))
xs=-log(z)/2
V={n: Phi(xs+1j*pi*n/2)+1j*pi*n*(xs+1j*pi*n/2) for n in range(-4,3)}
for n in V: print('n=%d  V_n='%n, nstr(V[n],10), '  V_n-V_0=',nstr(V[n]-V[0],10))
print('predicted V_{-1}-V_0 =', nstr(pi**2/8-1j*3*pi/4*log(2),10))
print('--- corrected base x_* with Phi_i\'(x_*)=0')
xst=-log(-z)/2
for n in range(-3,3):
    xn=xst+1j*pi*n/2
    print('n=%d x_n='%n,nstr(xn,6),' Phi\'(x_n)+i pi n=',nstr(Lw-2*xn-log(1-exp(-8*xn))/2+1j*pi*n,3),' V_n=',nstr(Phi(xn)+1j*pi*n*xn,10))
