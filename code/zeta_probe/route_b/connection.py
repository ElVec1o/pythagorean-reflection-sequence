import mpmath as mp
mp.mp.dps=50
exec(open('struct_probe.py').read().split('# The forward')[0])

# Homogeneous recursion operator: H L_b := L_{b+1} - A_b L_b + q L_{b-1}, A_b=(1+q)-2(1-q)q^{2b+1}.
# The TRUE source-0 solution L_b: from the derivation it solves the homogeneous eqn for b>=1
# (RHS source c_{b+1}-q c_b=0), with boundary L_0=0 and one inhomogeneous "kick" defining L_1.
# Let's find what L_1 is in terms of q. From raw: L_1 = (0 + c_1 + 2q u_1)/dd_1... messy.
# Instead: directly read L_1 from raw and fit b0 as a CONNECTION coefficient.
# Two homog solutions: phi (decaying-correction, ->1) and chi (->q^b mode).
# Build phi: solve homog forward with phi_inf=1. Easiest: backward from large B with
#   phi_B=1, phi_{B-1}=1 (the constant mode) then it auto-mixes; better integrate the
#   recursion forward in the b-decreasing direction is unstable. Use the q^b decay basis.

def homog_solutions(q,B):
    q=mp.mpf(q)
    A=lambda b:(1+q)-2*(1-q)*q**(2*b+1)
    # Solution P: P_0=1,P_1=1  (will tend to const+small q^b)
    # Solution Q: Q_0=0,Q_1=1
    def run(L0,L1):
        L=[mp.mpf(L0),mp.mpf(L1)]
        for b in range(1,B):
            L.append(A(b)*L[b]-q*L[b-1])
        return L
    return run(1,1),run(0,1)

q=mp.mpf('0.9'); B=300
b0,b1,t0,t1,L0arr,L1arr=raw(q,B if B<int(50/(1-q)) else int(50/(1-q)))
N=int(50/(1-q))
b0,b1,t0,t1,L0arr,L1arr=raw(q,N)
L=[mp.mpf(0)]+L0arr
P,Q=homog_solutions(q,N)
# True L = L_0=0 so L = L_1 * Q  (since Q_0=0,Q_1=1 and L_0=0,L_1=L[1]).
print('L_1 from raw=',float(L[1]))
# check L = L[1]*Q
err=max(abs(L[1]*Q[b]-L[b]) for b in range(0,N))
print('max |L[1]*Q - L|=',float(err))
# So b0=L_inf = L[1]*Q_inf. Need Q_inf (limit of Q_b).
print('Q tail:',[float(Q[b]) for b in range(N-5,N)])
print('b0=',float(b0),' L[1]*Q_inf approx=',float(L[1]*Q[N-1]))
