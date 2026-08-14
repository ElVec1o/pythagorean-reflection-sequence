import mpmath as mp, numpy as np
mp.mp.dps=40
# STRUCTURAL ROUTE (rigorous, classical):
# g(tau) is the amplitude series of Y3 ~ (3/sqrt2) tau^{3/2} sin(w)(1+g), w=sqrt(2/tau).
# The confluent eqn rescaled s=x/sqrt(tau): u_ss+(2-2/s^2)u=0, solution u=sqrt(s)C_{3/2}(sqrt2 s),
# a BESSEL fn of order nu=3/2. Evaluation at s=1/sqrt(tau): argument z=sqrt2 s=sqrt2/sqrt(tau)=w.
# So Y3(1/q)/leading is governed by the LARGE-ARGUMENT ASYMPTOTIC of J_{3/2}(w) (and Y_{3/2}),
# z=w=sqrt(2/tau).
#
# CLASSICAL FACT (Watson, DLMF 10.17): for fixed nu, the Hankel asymptotic series
#   H^{(1)}_nu(z) ~ sqrt(2/(pi z)) e^{i(z-nu pi/2-pi/4)} sum_{k>=0} i^k a_k(nu)/z^k
# has a_k(nu) = (4nu^2-1)(4nu^2-9)...(4nu^2-(2k-1)^2)/(k! 8^k).
# For nu=3/2: 4nu^2=9, so a_k = (9-1)(9-9)(9-25).../ ... => a_1=(9-1)/8=1, a_2=(9-1)(9-9)/(2 64)=0!
# nu=3/2 is HALF-INTEGER => the asymptotic series TERMINATES (J_{3/2} is elementary):
#   J_{3/2}(z)=sqrt(2/(pi z))( sin z / z - cos z ).  FINITE. So the *Bessel* series has NO tail.
nu=mp.mpf(3)/2
print("Hankel asymptotic coeffs a_k(nu=3/2) (DLMF 10.17.1):")
def ak(nu,k):
    num=mp.mpf(1)
    for j in range(1,k+1):
        num*= (4*nu**2-(2*j-1)**2)
    return num/(mp.factorial(k)*mp.mpf(8)**k)
for k in range(0,6):
    print(f"  a_{k} = {ak(nu,k)}")
print("=> TERMINATES at k=1 (a_2=0): J_{3/2} elementary. The Bessel series is NOT the source of g's tail.")
print()
# So g's Gevrey-1 tail does NOT come from the fixed-Bessel asymptotics (those terminate).
# It comes from the CONFLUENCE: q=e^{-tau} vs the continuum limit. The actual eq is the
# q-DIFFERENCE eq:qdiff, whose continuum limit is Bessel but with O(tau) corrections at every order.
# THIS is the real source: g = (q-Bessel)/(Bessel) - 1, an asymptotic series in tau whose Borel
# transform's singularities are the q-difference 'connection' constants.
print("CONCLUSION: the tail is the q-deformation (Bessel->q-Bessel) correction, Gevrey-1 in tau.")
print("The fixed-Bessel route does NOT by itself give the Borel sing (series terminates).")
print("Need the q-difference connection problem. Structural pinning is genuinely q-Bessel-tier.")
