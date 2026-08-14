import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# WKB / continuum reduction of t1 = sum_n 2q^{3n}/(y_n y_{n-1}).
# Set t=q^n (so n=ln t/ln q, dn = dt/(t ln q) = -dt/(t tau)). Sum -> integral:
#   t1 = sum_n f(n) ~ integral f(n) dn = integral_0^1 [2 t^3/y(t)^2] * (-1/(t tau)) dt  ... wait sign
# n from 1..inf, t=q^n from q down to 0. dn = dt/(t ln q)= -dt/(t tau). 
# t1 ~ int_{n=1}^{inf} 2q^{3n}/y_n^2 dn = int_{t=0}^{q} 2 t^3 / y(t)^2 * dt/(t tau)
#     = (1/tau) int_0^q 2 t^2/y(t)^2 dt.
# So t1 ~ (1/tau) * I,  I = int_0^1 2 t^2/y(t)^2 dt  (q~1).  For t1~tau/4 we'd need I~tau^2/4 -> 0?? 
# That can't be right because y(t) oscillates and the naive continuum FAILS (heavy cancellation, like SUM).
# Instead the mass is in the OSCILLATORY region; need the genuine WKB of y_n.
#
# The bulk dressing y_n: known (from memory) the bulk resolvent L_b ~ b0 sin(w(1-q^b))/sin w in boundary layer.
# y_n is the COMPANION (P22) solution. Let's just confirm the continuum naive integral does NOT give 1/4,
# documenting the gap honestly, then check the boundary-layer Bessel form.
i=8
q=poles[i-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
mp.mp.dps=50+int(2.0*float(w)); N=int(60/(1-q))
# y in boundary layer: variable W_b = w(1-q^n) (phase). near n small, q^n~1-n tau, W_b~w n tau = n tau w.
# Actually w(1-q^n)~ w*n*tau = n*tau*sqrt(2/tau)=n sqrt(2 tau). Spacing dphase= sqrt(2tau).
def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh
yh=cocyc_y(q,N)
# Test boundary-layer ansatz y_n ~ C * something(phase). Print y_n vs phase u=w(1-q^n)=w(1-t)
print(f"m={i} tau={float(tau):.5f} w={float(w):.3f}")
print(" n   u=w(1-q^n)   y_n      y_n/?  ")
qn=mp.mpf(1)
for n in [1,2,3,5,10,20,40,80,160,320]:
    t=q**n; u=w*(1-t)
    print(f" {n:>4} {float(u):>10.4f} {float(yh[n]):>10.5f}")
