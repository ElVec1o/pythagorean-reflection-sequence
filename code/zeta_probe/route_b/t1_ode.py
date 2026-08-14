import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# Continuum ODE. Cocycle step (small tau, q=e^{-tau}, t=q^n in (0,1)):
#  x_n = x_{n-1}(1+2q2n) - 2 y_{n-1} qn
#  y_n = 2 x_{n-1} q3n + y_{n-1}(1-2q2n)
# with qn=q^n=t, q2n=t^2, q3n=t^3.  Step in n; dn corresponds to dt=-tau t dn (dt/dn=-tau t).
# Differences: x_n-x_{n-1}=2 t^2 x_{n-1} - 2 t y_{n-1};  y_n-y_{n-1}=2t^3 x_{n-1}-2t^2 y_{n-1}.
# d/dn = -tau t d/dt. So:
#  -tau t x' = 2t^2 x - 2t y  => x' = -(2t/tau) x + (2/tau) y
#  -tau t y' = 2t^3 x - 2t^2 y => y' = -(2t^2/tau) x + (2t/tau) y
# From 2nd: x = (tau/(2t^2))[ (2t/tau) y - y' ] = (1/t) y - (tau/(2t^2)) y'.
# Plug into nothing-- differentiate to get 2nd order for y. Let me just verify numerically that 
# y_n solves y'' + (1/t) y' + (4/tau^2) y = 0  (Bessel J_0(2 w_eff ... )) form? guess.
# Actually let me derive: from y'=-(2t^2/tau)x+(2t/tau)y and x'=-(2t/tau)x+(2/tau)y.
# Let me just NUMERICALLY check the continuum ODE coefficients via finite differences on y_n.
def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh

# From the two first-order eqs eliminate x:
#  x = (1/t)y - (tau/(2t^2)) y'.    (E)
#  x' = -(2t/tau)x + (2/tau)y.
# differentiate E: x' = -(1/t^2)y + (1/t)y' - (tau/(2t^2))y'' + (tau/t^3) y'.
# set equal: -(1/t^2)y+(1/t)y'-(tau/(2t^2))y''+(tau/t^3)y' = -(2t/tau)[(1/t)y-(tau/(2t^2))y'] + (2/tau)y
#  RHS = -(2/tau)y + (1/t)y' + (2/tau)y = (1/t) y'.
# LHS: -(1/t^2)y+(1/t)y'-(tau/(2t^2))y''+(tau/t^3)y'.
# So: -(1/t^2)y -(tau/(2t^2))y'' +(tau/t^3)y' = 0  (the (1/t)y' cancels).
# Multiply by -2t^2/tau: (2/tau) y + y'' - (2/t) y' = 0.
#  => y'' - (2/t) y' + (2/tau) y = 0.    <-- continuum ODE for the cocycle y(t).
# Verify numerically.
q=poles[8-1]; tau=-mp.log(q); N=int(60/(1-q))
mp.mp.dps=60
yh=cocyc_y(q,N)
print("Verify ODE y'' - (2/t)y' + (2/tau)y = 0 at sample n (finite diff in n, convert to t):")
for n in [50,100,200,400]:
    t=q**n
    # use central diff in n. dt/dn=-tau t. y'(t)=dy/dn /(dt/dn). 
    yp_n=(yh[n+1]-yh[n-1])/2
    ypp_n=yh[n+1]-2*yh[n]+yh[n-1]
    dtdn=-tau*t
    yp_t=yp_n/dtdn
    # y''(t): d/dt(y'(t)) = (d/dn y'_t)/(dt/dn). approximate y'_t at n+/-... just use ypp in n:
    # y'(t)=yp_n/dtdn; d/dn[y'(t)] = ... easier: y''_t=(ypp_n - yp_n*d/dn ln|dtdn|)/dtdn^2
    # d/dn ln|dtdn|=d/dn ln(tau t)=d/dn(ln t)= -tau. so:
    ypp_t=(ypp_n - yp_n*(-tau))/dtdn**2
    res=ypp_t - (2/t)*yp_t + (2/tau)*yh[n]
    print(f" n={n} t={float(t):.5f} y={float(yh[n]):.5f} residual={float(res):.3e}")
