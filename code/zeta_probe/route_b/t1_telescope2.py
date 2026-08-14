import mpmath as mp
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# Within the SAME cocycle, (x_n,y_n) is one solution; the companion is (X_n,Y_n).
# But there's another companion: ratio r_n=x_n/y_n. 
# x,y solve: x_n=x_{n-1}(1+2q2n)-2y_{n-1} qn,  y_n=2x_{n-1}q3n+y_{n-1}(1-2q2n).
# Consider the ratio r_n = x_n / y_n. We found t1 = Y_N/y_N = sum 2q3n/(y_n y_{n-1}).
# Note Wronskian X_n y_n - Y_n x_n =1 => Y_n/y_n = (X_n y_n -1)/(x_n y_n)... messy.
# 
# Alternative: maybe sum 2q3n/(y_n y_{n-1}) telescopes against x_n/y_n.
# d(x_n/y_n) = (x_n y_{n-1}-x_{n-1}y_n)/(y_n y_{n-1}).
# x_n y_{n-1}-x_{n-1}y_n = [x'(1+2q2n)-2y'qn]y' - x'[2x'q3n+y'(1-2q2n)]   (primes=n-1)
#   = x'y'(1+2q2n) -2y'^2 qn -2x'^2 q3n -x'y'(1-2q2n)
#   = x'y'(4q2n) -2qn(y'^2+x'^2 q2n)
#   = 2qn[2x'y'q n... ] hmm let me just compute numerically what x_n y_{n-1}-x_{n-1}y_n is.
def cocyc_xy(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); xh=[x];yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; xh.append(x);yh.append(y)
    return xh,yh

q=mp.mpf('0.85');N=40
xh,yh=cocyc_xy(q,N)
qn=mp.mpf(1)
print("n  (x_n y_{n-1}-x_{n-1}y_n)    -2 q^n (y_{n-1}^2+...)")
for n in range(1,8):
    qn=qn*q
    val=xh[n]*yh[n-1]-xh[n-1]*yh[n]
    print(f"{n}  {float(val):>12.6f}")
