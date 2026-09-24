# P1g_scope.py -- VERIFIED (floating numpy, scoping only): Z, Z^pm, omega and the normalised transfer factors
#   G1=(1-z^2)/z - t1, G2=(1-z)/z - t1, G3(x)=t1+(1+x)/(2x), G4(x)=t1(1-x+z)+(1+z)/(2x), x=+-sqrt z, t1=-(1+omega)/2
# at all reduced a/N, N0<=N<=N1, N<=5a<=4N, a/N != 1/2.  Prints min margin and where.
import sys, numpy as np
from math import gcd
def data(a, N, M=None):
    z = np.exp(2j*np.pi*a/N); c = -2*(1-z)
    X = c**N if N*np.log(abs(c)) < 300 else np.inf
    if np.isfinite(X):
        B = 2+X; w = 2/(B*(1+np.sqrt(1-4/(B*B)))); u = np.exp(2*np.log(1-w)/N)/c
    else: u = 1/c
    if M is None: M = int(60/(-np.log(abs(u))))+10
    n = np.arange(1, M+1); msk = (n % N) != 0
    cn = np.where(msk, u**n/(n*(1-z**(-n.astype(float)))+(~msk)), 0)
    k = np.arange(N)
    Ph = np.array([np.sum(cn*z**(kk*n)) for kk in k])
    b = np.exp(Ph)
    nu = np.arange(N)
    def gam(sh): return np.array([np.mean(z**(-(nu*nu+sh*nu+kk*nu) % N)) for kk in k])
    Z = np.sum(gam(0)*b); Zp = np.sum(gam(1)*b); Zm = np.sum(gam(-1)*b)
    return z, u, Z, Zp, Zm
def margins(z, u, Zp, Zm):
    om = Zm/(u*Zp); t1 = -(1+om)/2
    G = [(1-z*z)/z - t1, (1-z)/z - t1]
    s = np.sqrt(z)
    for x in (s, -s): G += [t1+(1+x)/(2*x), t1*(1-x+z)+(1+z)/(2*x)]
    return om, t1, [abs(g) for g in G]
if __name__ == '__main__':
    N0, N1 = int(sys.argv[1]), int(sys.argv[2])
    worst = (9, None); minZ = 9
    for N in range(N0, N1+1):
        for a in range(1, N):
            if gcd(a, N) != 1 or not (N <= 5*a <= 4*N) or 2*a == N: continue
            z, u, Z, Zp, Zm = data(a, N)
            om, t1, G = margins(z, u, Zp, Zm)
            minZ = min(minZ, abs(Zp), abs(Zm))
            m = min(G)
            if m < worst[0]: worst = (m, (a, N, int(np.argmin(G)), om))
    print('min |Z^pm| %.4f ; min margin %.4f at %s' % (minZ, worst[0], worst[1]))
