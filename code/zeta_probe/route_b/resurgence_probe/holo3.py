import mpmath as mp, pickle
mp.mp.dps = 50
an=[mp.mpf(s) for s in pickle.load(open('/tmp/an_vals.pkl','rb'))]
bn=[mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]
# Sharper: if a P-recurrence of (J,D) truly held, then for ALL larger row-counts the same
# null vector persists. Test: fit null vector on FIRST part, predict the LAST coefficient.
def predict_last(seq,J,D):
    nun=(J+1)*(D+1)
    rows_fit=len(seq)-J-1  # leave last eqn out
    if rows_fit < nun: return None
    A=mp.matrix(rows_fit,nun)
    for i in range(rows_fit):
        n=i; col=0
        for j in range(J+1):
            for d in range(D+1):
                A[i,col]=mp.mpf(n)**d*seq[n+j]; col+=1
    # find approx null vector (right singular vector of smallest sing val)
    U,S,V=mp.svd(A)
    v=V[nun-1,:]  # last row of V = smallest sing vector
    vv=[v[0,c] for c in range(nun)]
    # check residual on the HELD-OUT last equation
    n=len(seq)-1-J; col=0; resid=mp.mpf(0); scale=mp.mpf(0)
    for j in range(J+1):
        for d in range(D+1):
            resid+=vv[col]*mp.mpf(n)**d*seq[n+j]; col+=1
    # scale = typical term
    scale=abs(seq[n+J])*sum(abs(x) for x in vv)
    return abs(resid)/scale if scale>0 else None
print("Held-out P-recurrence prediction (genuine holonomy => resid ~ 1e-40):")
for name,seq in [('g',an),('B',bn)]:
    print(f"  {name}:")
    for (J,D) in [(2,1),(2,2),(3,1),(1,3),(3,2)]:
        r=predict_last(seq,J,D)
        if r is not None:
            print(f"    J={J} D={D}: held-out resid/scale = {mp.nstr(r,4)}")
