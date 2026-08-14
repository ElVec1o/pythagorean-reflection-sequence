"""
G3 attack via AMPLITUDE-PHASE (Prufer): convert the oscillatory cancellation into amplitude x sin(phase).
Rescale z_n = q^{-3n/2} y_n => symmetric recursion  z_{n+1}+z_{n-1}=b_n z_n,  b_n=a_n/q^{3/2}.
Oscillatory where b_n<2 (local wavenumber k_n=arccos(b_n/2)); turning point n* where b_{n*}=2.
Prufer: z_n=R_n sin(Theta_n), z_{n-1}=R_n sin(Theta_n - k_n).  R_n^2=(z_n^2+z_{n-1}^2-2cos(k_n)z_n z_{n-1})/sin^2(k_n).
SUBATOMS of G3:
  3a  amplitude R_n bounded/slowly-varying (NO cancellation)?   (the 'easy' factor)
  3b  turning point n* location + Airy connection (the oscill->expon transition)
  3c  the PHASE at the pole carries the suppression (P12 small <=> sin(Theta_*) small)?
"""
import mpmath as mp
mp.mp.dps=40

def Sig_t(q):
    q=mp.mpf(q);S=mp.mpf(0);pr=mp.mpf(1)
    for j in range(int(220/(1-q))+50):
        kk=1+2*j;S+=2*q/(1-q**(kk+1))*pr;pr*=2*q**(kk+3)/(1-q**(kk+2))-2*q**(kk+2)/(1-q**(kk+1))
        if abs(pr)<mp.mpf(10)**(-mp.mp.dps-10):break
    return S
def refine(q0,it=16):
    q=mp.mpf(q0);h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(it):
        f0=Sig_t(q)-1;fp=(Sig_t(q+h)-Sig_t(q-h))/(2*h);q=q-f0/fp
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

def y2_seq(q,N):
    """P12-sequence: 2nd component of [1;0]-init trajectory; ->P12 as n->inf."""
    a,b=mp.mpf(1),mp.mpf(0); seq=[b]; qn=mp.mpf(1)
    for n in range(1,N+1):
        qn*=q;q2n=qn*qn;q3n=q2n*qn
        a,b=a*(1+2*q2n)-2*b*qn, 2*a*q3n+b*(1-2*q2n); seq.append(b)
    return seq

m=8
q=refine(poles[m-1]); tau=-mp.log(q); w=mp.sqrt(2/tau)
N=int(min(120, 7/(1-q)))
y=y2_seq(q,N)
P12=y[-1]
print(f"G3 Prufer analysis at m={m}, tau={float(tau):.5f}, w={float(w):.3f}, P12={mp.nstr(P12,8)} (~{float(P12/tau**1.5):.4f} tau^1.5)")
# rescale + Prufer
z=[q**(-mp.mpf(3)*n/2)*y[n] for n in range(N+1)]
print(f"\n{'n':>4}{'b_n':>12}{'k_n=acos(b/2)':>14}{'z_n':>14}{'R_n (amp)':>14}{'sin(Theta_n)':>13}")
nstar=None
for n in range(1,N):
    bn=(1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
    if abs(bn)<=2:
        kn=mp.acos(bn/2)
        Rn=mp.sqrt((z[n]**2+z[n-1]**2-2*mp.cos(kn)*z[n]*z[n-1])/mp.sin(kn)**2)
        sinTh=z[n]/Rn if Rn!=0 else mp.mpf(0)
    else:
        if nstar is None: nstar=n
        kn=mp.mpf('nan');Rn=mp.mpf('nan');sinTh=mp.mpf('nan')
    if n<=12 or n%10==0 or (nstar and abs(n-nstar)<=2):
        print(f"{n:>4}{float(bn):>12.6f}{float(kn) if kn==kn else float('nan'):>14.6f}{mp.nstr(z[n],6):>14}{mp.nstr(Rn,6) if Rn==Rn else 'expon':>14}{mp.nstr(sinTh,5) if sinTh==sinTh else '-':>13}")
print(f"\nturning point n* (b_n crosses 2) ~ {nstar}  (predicted log(8/(9 tau))/(2 tau) = {float(mp.log(8/(9*tau))/(2*tau)):.1f})")
# 3a: is R_n bounded/slowly-varying in the oscillatory region?
Rs=[]
for n in range(2,(nstar or N)-1):
    bn=(1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
    if abs(bn)<2:
        kn=mp.acos(bn/2);Rn=mp.sqrt((z[n]**2+z[n-1]**2-2*mp.cos(kn)*z[n]*z[n-1])/mp.sin(kn)**2);Rs.append(Rn)
if Rs:
    print(f"3a AMPLITUDE R_n over oscillatory region: min={float(min(Rs)):.5g} max={float(max(Rs)):.5g} ratio={float(max(Rs)/min(Rs)):.3f}")
    print(f"   R_n*sqrt(k_n) (WKB invariant) const? first/last R*sqrt(k):")
    nn=[3,(nstar or N)//3,2*(nstar or N)//3]
    for n in nn:
        bn=(1+q**3-2*(1-q)*q**(2*n+2))/q**mp.mpf('1.5')
        if abs(bn)<2:
            kn=mp.acos(bn/2);Rn=mp.sqrt((z[n]**2+z[n-1]**2-2*mp.cos(kn)*z[n]*z[n-1])/mp.sin(kn)**2)
            print(f"     n={n}: R*sqrt(sin k)={float(Rn*mp.sqrt(mp.sin(kn))):.6g}")
print("\n=> if R*sqrt(sin k)=const (WKB adiabatic invariant) and bounded, 3a is the EASY factor;")
print("   the suppression of P12 then lives in sin(Theta) at the pole (3c) = the pole-condition phase.")
