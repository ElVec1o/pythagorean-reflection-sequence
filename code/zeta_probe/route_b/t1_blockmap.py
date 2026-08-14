import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])

def raw_full(q,N):
    qp=[mp.mpf(1)]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; v[b-1]=vb
    return v,qp

# t0=Sum 2qb G_b = S1b/Se (PROVEN). 
# Define partial sums T0(m)=sum_{b=1}^m 2qb G_b, T1(m)=sum 2q2b G_b.
# Relationship: G_b weight q^b extra.
# Connect to bulk block: S1b = Sbulk(1,q) = sum_j alpha(1+2j) prod gamma. 
# t0 = S1b/(1-S1b). So sum 2qb G_b = S1b/(1-S1b).
#
# CANDIDATE: t1 might equal a y-derivative of the bulk block.
# The bulk block S1b depends on q only. But the resolvent source carries an extra param.
# In the cycle-bridge dictionary, t1 is the SECOND moment / s=g_V t1.
# Let's directly hunt: t1 =? f(S0b,S1b,S2b,S3b, derivatives).
# Test a few structured guesses informed by t0=S1b/Se=S1b/(1-S1b):
print("Hunt t1 as rational combos. Se=1-S1b.")
print(f"{'q':>7} {'t1':>12} {'(S1b-S2b)/Se':>13} {'(S0b-S1b)/Se':>13} {'S2b/Se':>11} {'(S1b-S2b)/Se^2':>15}")
for qf in ['0.70','0.80','0.88','0.96','0.985']:
    q=mp.mpf(qf); p=1-q; N=int(70/(1-q))
    v,qp=raw_full(q,N)
    A=[None]*(N+1);B=[None]*(N+1)
    for b in range(1,N+1):
        qb=qp[b];q2b=qb*qb
        A[b]=1+2*q2b+2*qb*v[b-1];B[b]=qb+v[b-1]
    G=[None]*(N+1);pref=mp.mpf(1)
    for b in range(1,N+1): G[b]=pref*B[b];pref*=A[b]
    t1=sum(2*qp[b]**2*G[b] for b in range(1,N+1))
    S0b=Sbulk(0,q);S1b=Sbulk(1,q);S2b=Sbulk(2,q);S3b=Sbulk(3,q);Se=1-S1b
    print(f"{qf:>7} {float(t1):>12.6f} {float((S1b-S2b)/Se):>13.6f} {float((S0b-S1b)/Se):>13.6f} {float(S2b/Se):>11.6f} {float((S1b-S2b)/Se**2):>15.6f}")
