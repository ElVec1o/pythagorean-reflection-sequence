import json, cmath, math
from fractions import Fraction
z=[complex(a,b) for a,b in json.load(open('roots_hi.json'))]
z=[w for w in z if abs(w)<0.97]
z.sort(key=lambda w: cmath.phase(w))
# angular gaps: largest gap in arg among zeros (upper half), per radius band
for R in [0.9,0.94,0.97]:
    a=sorted([0.0]+[cmath.phase(w)/(2*math.pi) for w in z if abs(w)<R]+[0.5])
    gaps=[(a[i+1]-a[i],a[i],a[i+1]) for i in range(len(a)-1)]
    g=max(gaps)
    print('R=%.2f  n_upper=%d  largest arg gap (in units of 2pi) = %.4f between %.4f and %.4f'%(R,len(a)-2,*g))
# track zeros approaching a few roots of unity: within angular distance < 0.6*(1-|q|)*... just list those nearest
def near(a_over_k, tol):
    t=2*math.pi*a_over_k
    L=[w for w in z if abs(cmath.phase(w)-t)<tol]
    return sorted(L,key=abs)
for fr in [Fraction(1,2),Fraction(1,3),Fraction(1,4),Fraction(1,5),Fraction(2,5),Fraction(1,6),Fraction(1,8),Fraction(3,8),Fraction(1,12)]:
    L=near(float(fr),0.25)
    zeta=cmath.exp(2j*math.pi*float(fr))
    print('zeta=e^{2pi i %s}: '%fr, ' '.join('[|q|=%.4f d=%.4f dir=%.2fdeg]'%(abs(w),abs(w-zeta),math.degrees(cmath.phase((w-zeta)/(-zeta)))) for w in L[:10]))
