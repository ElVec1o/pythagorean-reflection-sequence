# P1a: distribution of |Gcal| / (max|W_m| * sqrt(2|theta|)) over p/q (good arc), theta, admissible N mod 4q|theta|.
# Usage: perl -e 'alarm 290; exec @ARGV' python3 P1a_gauss.py QMAX THMAX
import sys
from collections import Counter
from math import gcd
exec(open(__file__.replace('P1a_gauss.py', 'P1a_amp.py')).read().split('if __name__')[0])
QMAX, THMAX = int(sys.argv[1]), int(sys.argv[2])
cnt = Counter(); ex = {}
for q in range(2, QMAX+1):
    for p in range(1, q//2+1):
        if gcd(p, q) != 1 or 4*sin(pi*p/q) < exp(0.05): continue
        for theta in [t for t in range(-THMAX, THMAX+1) if t != 0]:
            ms, W = weights(p, q, theta); w0 = max(abs(w) for w in W)
            for n in range(1, 4*q*abs(theta), 2):
                if (p*n+theta) % q: continue
                G = sum(exp(-1j*pi*m*m*n/(2*q*theta))*w for m, w in zip(ms, W))
                key = (round(float(abs(G)/(w0*sqrt(2*abs(theta)))), 6), q % 4 if q % 2 == 0 else 'odd')
                cnt[key] += 1; ex.setdefault(key, (p, q, theta, n))
for k in sorted(cnt): print('ratio', k[0], 'q class', k[1], 'count', cnt[k], 'example p,q,theta,N', ex[k])
