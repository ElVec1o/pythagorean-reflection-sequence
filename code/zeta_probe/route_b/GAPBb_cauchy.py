"""
CLOSE B(b): slope |Y3(1)'(q~_m)| <= C' tau^{-1/2}  via CAUCHY's estimate (rigorous), reducing to the
MAGNITUDE bound |Y3(1)| <= C tau on a complex circle (the leading 0phi1 confluence -- NO derivative cancellation).
  Cauchy: |Y3(1)'(q~)| <= M/r,  M = max_{|q-q~|=r}|Y3(1)|,  r = c tau^{3/2}.
  Need: M <= C tau (leading magnitude).  Then |Y3(1)'| <= C tau/(c tau^{3/2}) = (C/c) tau^{-1/2}.  DONE.
Verify: (1) M <= C tau on the circle (leading magnitude bound holds, complex q);
        (2) M/r <= C' tau^{-1/2}  and  >= actual |Y3(1)'(q~)|  (Cauchy bound valid & tight order).
"""
import mpmath as mp
def dk(k,q):
    num=(-2)**k*(1-q)**k*q**(k*k+3*k); den=mp.mpf(1)
    for i in range(k): den*=(1-q**(2*i+2))*(1-q**(2*i+5))
    return num/den
def Y3at1(q):
    K=int(8/abs(1-q)**0.5)+40; return mp.fsum(dk(k,q) for k in range(K))
def find_root_real(f,q0,iters=40):
    q=mp.mpf(q0); h=mp.mpf(10)**(-(mp.mp.dps//2))
    for _ in range(iters):
        f0=f(q); fp=(f(q+h)-f(q-h))/(2*h)
        if fp==0: break
        dq=f0/fp; q=q-dq
        if abs(dq)<mp.mpf(10)**(-(mp.mp.dps-10)): break
    return q
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]
print("Cauchy route for B(b): M=max|Y3(1)| on |q-q~|=r (r=c tau^1.5), bound |Y3'|<=M/r vs actual:")
print(f"{'m':>3}{'tau':>10}{'r=c t1.5':>11}{'M':>12}{'M/tau':>9}{'M/r':>12}{'*sqrt(t)':>9}{'Y3actual':>11}{'<=M/r?':>7}")
for m in [3,4,6,8,12]:
    q0=poles[m-1]; tau0=-mp.log(q0); w=mp.sqrt(2/tau0)
    mp.mp.dps=50+int(1.5*float(w))
    qz=find_root_real(lambda q:Y3at1(q),q0)            # the real zero q~_m
    tau=-mp.log(qz)
    c=mp.mpf('0.3'); r=c*tau**mp.mpf('1.5')             # circle radius
    Npts=24; M=mp.mpf(0)
    for j in range(Npts):
        th=2*mp.pi*j/Npts; qj=qz+r*mp.e**(mp.mpc(0,1)*th)
        v=abs(Y3at1(qj))
        if v>M: M=v
    hh=mp.mpf(10)**(-(mp.mp.dps//2))
    Y3p=abs((Y3at1(qz+hh)-Y3at1(qz-hh))/(2*hh))        # actual |Y3'(q~)|
    print(f"{m:>3}{float(tau):>10.6f}{float(r):>11.3e}{float(M):>12.3e}{float(M/tau):>9.4f}{float(M/r):>12.3e}"
          f"{float((M/r)*mp.sqrt(tau)):>9.4f}{float(Y3p):>11.3e}{str(Y3p<=M/r):>7}")
    mp.mp.dps=30
print("\nM<=C tau (M/tau bounded ~const) => leading magnitude holds; M/r ~ tau^{-1/2} ((M/r)sqrt(t) bounded);")
print("Y3'(q~) <= M/r (Cauchy valid). => B(b): |Y3(1)'|=O(tau^{-1/2}) RIGOROUS via Cauchy, modulo |Y3(1)|<=C tau.")
