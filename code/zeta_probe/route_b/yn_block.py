import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])

# Now: is y_n a known block partial sum? y_inf = Se = 1-S1b. 
# Recall Se = sum_j (-2p)^j q^{j(j+1)}/(q;q)_{2j} (the prompt closed form).
# The cocycle y_n is a partial product; let's see if y_n equals the truncated Se series.
def cocyc_y(q,N):
    x=mp.mpf(0);y=mp.mpf(1);qn=mp.mpf(1); yh=[y]
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        x,y=xn,yn; yh.append(y)
    return yh

# Se truncated to use first n cocycle steps -> compare
q=mp.mpf('0.80'); N=int(70/(1-q)); p=1-q
yh=cocyc_y(q,N)
poch=[mp.mpf(1)]
for nn in range(1,2*N+2): poch.append(poch[-1]*(1-q**nn))
print("n   y_n        Se_trunc(j<=?)")
for n in [1,2,3,5,10,20]:
    # Se converges fast; just show y_n approaching Se
    print(f"{n:>2} {float(yh[n]):>12.7f}")
print(f"Se(full)={float(1-Sbulk(1,q)):.7f}  y_N={float(yh[N]):.7f}")
