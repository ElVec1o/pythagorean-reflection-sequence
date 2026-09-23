import sys
args=sys.argv[1:]; sys.argv=['x','1','3']
exec(open('k1.py').read().split('a,N=int')[0])
a,N,n1,n2,DPS=[int(u) for u in args[:5]]; js=[int(u) for u in args[5:]]
mp.dps=30
z,L,w,xs,A,V,Phi=setup(a,N); dV=V(n2)-V(n1); lg=log(-A(n1)/A(n2))
for j in js:
  mp.dps=30; u=(lg+2j*pi*j)/dV; t0=1/u
  print('j',j,'t0',nstr(t0,6),'arg deg',nstr(arg(t0)*180/pi,6),'Re u',nstr(re(u),4),flush=True)
  mp.dps=DPS; z=exp(2j*pi*a/N)
  try:
    ts=findroot(lambda tt:Bser(z*exp(-tt)),(t0,t0*(1+mpf(10)**-6)),solver='secant',tol=mpf(10)**-25,maxsteps=30)
    v1=abs(Bser(z*exp(-ts))); v2=abs(Bser(z*exp(-ts*(1+mpf(10)**-4))))
    print('   t*',nstr(ts,10),'|1/t*-1/t0|',nstr(abs(1/ts-u),4),'spacing',nstr(2*pi/abs(dV),4),'|B(t*)|',nstr(v1,3),'|B(t*(1+1e-4))|',nstr(v2,3),flush=True)
  except Exception as e: print('   fail',str(e)[:70])
