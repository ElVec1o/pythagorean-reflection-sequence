import mpmath as mp
mp.mp.dps=50
def Sigma1T(tau):
    q=mp.e**(-tau); s=mp.mpf(0); k=0; poch2=(1-q**2); poch3=mp.mpf(1)
    tol=mp.mpf(10)**(-mp.mp.dps-12)
    while True:
        num=2*q*(-2*(1-q))**k*q**(k*k+2*k); term=num/(poch2*poch3); s+=term
        if k>5 and abs(term)<tol*abs(s): break
        if k>6000: break
        k+=1; poch2*=(1-q**2*q**(2*k)); poch3*=(1-q**3*q**(2*(k-1)))
    return s
# critical points S'(tau*)=0 in complex tau. Use the value reported by prior agent:
# Re0=0.880788260021, arg0=2.096796136359, tau*_0=Re0 +- i*arg0 (first rung).
# Find it fresh via findroot of S'(tau)=0 near a complex seed.
def Sp(tau):
    h=mp.mpf(10)**(-25)
    return (Sigma1T(tau+h)-Sigma1T(tau-h))/(2*h)
seeds=[mp.mpc('0.88','2.10'), mp.mpc('0.88','-2.10')]
crit=[]
for s in seeds:
    try:
        tc=mp.findroot(Sp, s)
        crit.append(tc)
        print(f"S'(tau*)=0 at tau*={mp.nstr(tc,12)}  S(tau*)={mp.nstr(Sigma1T(tc),8)}")
    except Exception as e:
        print("crit fail",e)
if crit:
    tc=crit[0]
    print(f"\n  tau*   = {mp.nstr(tc,12)}  |tau*|={float(abs(tc)):.4f} arg={float(mp.arg(tc)*180/mp.pi):.2f}")
    print(f"  2 tau* = {mp.nstr(2*tc,12)}  |2tau*|={float(abs(2*tc)):.4f} arg={float(mp.arg(2*tc)*180/mp.pi):.2f}")
    print(f"\nMEASURED amplitude Borel singularity A0: Re~2.6, Im~4.9, |A0|~5.5, arg~61.8 deg")
    print(f"Compare 2tau*: does it match the amplitude singularity location?")
    # also tau* itself, 3tau*, etc.
    for fac in [1,2,3]:
        z=fac*tc
        print(f"  {fac}*tau*: Re={float(z.real):.3f} Im={float(abs(z.imag)):.3f} |.|={float(abs(z)):.3f} arg={float(abs(mp.arg(z))*180/mp.pi):.2f}")
