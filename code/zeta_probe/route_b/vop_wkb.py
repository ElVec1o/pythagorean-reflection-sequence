import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# Derive t1~tau/4 from VOP + WKB of y_n. 
# y_n solves the cocycle; its leading WKB (boundary layer, phase psi). 
# We KNOW (proven numerator/lem:cos engine): the cocycle solutions at phase w have the structure
# of Bessel J_0,Y_0 in the variable W=w(1-t)~ "travel phase". 
# y_n = P22: starts y_0=1 (the cos-type). x_n=P21-partial starts x_0=0 (sin-type, ->-S0b).
# Leading: y_n ~ cos(psi_n)*Amp, x_n ~ sin(psi_n)*Amp with SAME amplitude Amp_n (Wronskian-normalized).
# The product 1/(y_n y_{n-1}) with phase advancing by dpsi.
# t1=sum 2q^{3n}/(y_n y_{n-1}). With y_n~Amp_n cos(psi_n):
#   1/(y_n y_{n-1}) ~ 1/(Amp^2 cos psi_n cos psi_{n-1}).
# Sum of 2q^{3n}/(Amp^2 cos^2 psi) over n. Convert to integral over psi.
# This is messy; INSTEAD verify the WKB amplitude/phase numerically and confirm the integral -> tau/4.
#
# Direct numeric WKB extraction: from y_n, y_{n-1}, y_{n+1} extract local amplitude & phase.
i=8
q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
mp.mp.dps=60+int(2.2*float(w)); N=int(60/(1-q))
def cocyc_xy(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); xh=[x];yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; xh.append(x);yh.append(y)
    return xh,yh
xh,yh=cocyc_xy(q,N)
# Wronskian-type amplitude: A_n^2 ~ y_n^2 + (x_n * scale)^2. Since x=sin-type ampl. with factor.
# Check y_n^2 + x_n^2 * f -> smooth amplitude. From the ODE eigen-structure the conserved combo:
# For y''-(2/t)y'+(2/tau)y=0, the WKB amplitude ~ t / (2/tau)^{1/4}... 
# Just confirm t1/tau->1/4 robustly and that VOP integral approx works:
qn=mp.mpf(1); S=mp.mpf(0); terms=[]
for n in range(1,N+1):
    qn=qn*q; tm=2*qn**3/(yh[n]*yh[n-1]); S+=tm
print(f"m={i}: t1={float(S):.8f}, t1/tau={float(S/tau):.8f}")
# WKB amplitude check: plot R_n=sqrt(y_n^2 + (tau/2)* something). 
# Conserved quantity for the recursion: from cocycle det, y_n x_{n-1}-y_{n-1}x_n relates.
# Print y_n^2 + (2/tau) * x_n^2 *? to find smooth invariant
print(" n   t=q^n   y_n      x_n     y^2+ (w^2 t^2) x^2 ?")
qn=mp.mpf(1)
for n in [20,40,80,120,160]:
    t=q**n
    inv=yh[n]**2 + (w*t)**2 * xh[n]**2  # guess
    print(f" {n:>4} {float(t):.4f} {float(yh[n]):>9.4f} {float(xh[n]):>9.4f} inv={float(inv):>10.4f}")
