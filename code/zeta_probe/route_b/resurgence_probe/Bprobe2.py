import mpmath as mp, pickle
mp.mp.dps = 60
bn = [mp.mpf(s) for s in pickle.load(open('/tmp/bn_vals.pkl','rb'))]
an = [mp.mpf(s) for s in pickle.load(open('/tmp/an_vals.pkl','rb'))]
N = len(bn)

# The b_n sign pattern +----+++---+++ has period ~6 (after b_0). A pair of complex-conjugate
# branch points at t_s = R e^{+- i phi} gives b_n ~ Re(C (R e^{-i phi})^{-n} ...)? Actually a
# singularity of B at t_s=R e^{i phi} contributes b_n ~ |t_s|^{-n} cos(n phi + ...). Period 6 of
# the sign => phi ~ pi/3 (60 deg), and |t_s|=1/(lim |b_n|^{1/n}) ~ 1/0.21 ~ 4.76. Consistent
# with the off-axis branch cut at arg~60deg, |t_s|~4.5-6.
# Estimate t_s by fitting b_n ~ A r^{-n} cos(n phi + psi). Use ratios / 3-term recurrence.
# Linear-predictor (Prony) on last several b_n: find roots z with b satisfying sum c_j b_{n-j}=0.
M = 5  # predictor order
n0 = N - 2*M
rows = N - M - n0
A = mp.matrix(rows, M); rhs = mp.matrix(rows,1)
for i in range(rows):
    n = n0 + M + i
    rhs[i,0] = bn[n]
    for j in range(M):
        A[i,j] = bn[n-1-j]
# least squares
coef = mp.lu_solve(A.T*A, A.T*rhs)
# characteristic poly z^M - sum coef[j] z^{M-1-j}
poly = [mp.mpf(1)] + [-coef[j,0] for j in range(M)]
roots = mp.polyroots(poly, maxsteps=200, extraprec=200)
print("Prony roots z (b_n ~ sum z^n), singularities of B at t_s=1/z:")
for z in roots:
    if abs(z)>1e-9:
        ts = 1/z
        print(f"  z={mp.nstr(z,8)}  |1/z|={mp.nstr(abs(ts),8)}  arg(1/z)={mp.nstr(mp.arg(ts)*180/mp.pi,6)} deg")
