from mpmath import *
import sys
exec(open('k1count.py').read().split('path=[]')[0].replace("a,N=int(sys.argv[1]),int(sys.argv[2]); r1,r2=mpf(sys.argv[3]),mpf(sys.argv[4]); mp.dps=int(sys.argv[5])","a,N=1,14; mp.dps=int(sys.argv[1]); r1=r2=1").replace("thm=mpf(sys.argv[7] if len(sys.argv)>7 else 85)*pi/180","thm=1"))
for t0 in [mpc('9.4321998e-5','2.485103e-7'),mpc('8.0094877e-5','-1.0027548e-7'),mpc('5.1982095e-5','-4.9663437e-8')]:
  try:
    ts=findroot(lambda t:Bser(z*exp(-t))[0],(t0,t0*(1+1e-6)),solver='secant',tol=mpf(10)**-30)
    v,big=Bser(z*exp(-ts)); print('dps',mp.dps,'t*',nstr(ts,12),'|B|',nstr(abs(v),3),'max|b_k|',nstr(big,4),'|B(t*(1+1e-3))|',nstr(abs(Bser(z*exp(-ts*1.001))[0]),4))
  except Exception as e: print('fail',str(e)[:80])
