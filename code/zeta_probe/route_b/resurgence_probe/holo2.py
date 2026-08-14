import mpmath as mp, pickle
mp.mp.dps = 50
an=[mp.mpf(s) for s in pickle.load(open('/tmp/an_vals.pkl','rb'))]
bn=[mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]

def test_precurrence(seq, J, D):
    nun=(J+1)*(D+1)
    rows=len(seq)-J
    if rows < nun+1: return None,nun,rows
    A=mp.matrix(rows,nun)
    for i in range(rows):
        n=i; col=0
        for j in range(J+1):
            for d in range(D+1):
                A[i,col]=mp.mpf(n)**d * seq[n+j]; col+=1
    # column-normalize to compare singular values meaningfully
    for c in range(nun):
        nrm=mp.sqrt(sum(A[r,c]**2 for r in range(rows)))
        if nrm>0:
            for r in range(rows): A[r,c]/=nrm
    S=mp.svd(A, compute_uv=False)
    Sl=[abs(x) for x in S]
    return (min(Sl)/max(Sl)), nun, rows

for name,seq in [('g',an),('B',bn)]:
    print(f"--- {name}-series holonomy (smin/smax; ~0 => P-recurrence exists) ---")
    found=False
    for J in range(1,4):
        for D in range(0,4):
            r=test_precurrence(seq,J,D)
            if r[0] is None: continue
            ratio,nun,rows=r
            flag = "  <== candidate" if ratio<mp.mpf(10)**-8 else ""
            print(f"  J={J} D={D} (nun={nun},rows={rows}) cond_ratio={mp.nstr(ratio,4)}{flag}")
