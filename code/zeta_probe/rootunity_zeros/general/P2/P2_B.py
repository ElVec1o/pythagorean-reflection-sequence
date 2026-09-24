# P2_B.py -- evaluator for B(q)=sum_k (-2(1-q))^k q^{k^2}/(q;q)_{2k} in Arb (python-flint acb).
# Returns an acb ball (rigorous up to the explicit tail bound added below). Used by P2_scan.py / P2_cert.py.
from flint import acb, arb, ctx
import math
def Bq(q, prec=None, maxk=10**7):
    """q: acb or complex with |q|<1. Sum until the terms are below 2^-prec*max and
    the ratio test gives a geometric tail; the tail is added as a radius (rigorous)."""
    q = acb(q)
    ct = -2*(1-q)
    b = acb(1); S = acb(1); q2k1 = q  # q^{2k+1}
    q2 = q*q
    aq = float(abs(q).mid()); mx = 0.0; k = 0
    while True:
        # b_{k+1} = b_k * ct * q^{2k+1} / ((1-q^{2k+1})(1-q^{2k+2}))
        num = ct*q2k1
        b = b*num/((1-q2k1)*(1-q2k1*q))
        q2k1 = q2k1*q2; k += 1
        S += b
        lb = float(abs(b).mid()) if b.is_finite() else float('inf')
        if lb > mx: mx = lb
        if k > 5 and lb < 1e-40*max(mx,1) :
            # rigorous tail: ratio r_k=|ct||q|^{2k+1}/((1-|q|^{2k+1})(1-|q|^{2k+2})), decreasing once |q|^{2k}(...)<1
            aqa = abs(q).upper() if hasattr(abs(q),'upper') else abs(q)
            r = abs(ct)*abs(q2k1)/((1-abs(q2k1))*(1-abs(q2k1)*abs(q)))
            rr = float(r.mid())
            if rr < 0.5:
                tail = abs(b)*r/(1-r)
                S += acb(0, 0) + acb(arb(0, tail.mid()+tail.rad()), arb(0, tail.mid()+tail.rad()))
                return S, k, mx
        if k > maxk: raise RuntimeError('maxk')
