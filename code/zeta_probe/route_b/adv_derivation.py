import mpmath as mp
mp.mp.dps = 50

# Verify the c_k recursion claim:  c_k = 2(1-q) q c_{k-2} / ((1-q^k)(1-q^{1-k}))
# with k=0,1 free (c0=b0, c1).  And check b0 = c0, plus the SECOND boundary cond.
# The series claim: L_b = sum_{k>=0} c_k q^{kb}.  L_0 = sum c_k = 0.
# So given c0,c1 free and the recursion, L_0 = sum_k c_k = 0 fixes ONE relation between c0,c1.

# Let's test: with c1 = -2q/(1-q), does sum_k c_k = 0 give c0 = b0_closed?
def qpoch(q,n):
    p=mp.mpf(1)
    for i in range(1,n+1): p*=(1-q**i)
    return p

def b0_closed(q):
    onem=1-q
    Se=mp.mpf(0);So=mp.mpf(0)
    for j in range(0,300):
        te=(-2*onem)**j*q**(j*(j+1))/qpoch(q,2*j)
        to=(-2*onem)**j*q**(j*(j+2))*onem/qpoch(q,2*j+1)
        Se+=te;So+=to
        if j>5 and abs(te)+abs(to)<mp.mpf(10)**(-60):break
    return (2*q/onem)*So/Se

def build_c(q, c0, c1, K=400):
    c=[mp.mpf(0)]*(K+2)
    c[0]=c0; c[1]=c1
    for k in range(2,K+1):
        denom=(1-q**k)*(1-q**(1-k))
        c[k]=2*(1-q)*q*c[k-2]/denom
    return c

for q in [mp.mpf('0.8'),mp.mpf('0.9'),mp.mpf('0.95')]:
    onem=1-q
    c1=-2*q/onem
    b0c=b0_closed(q)
    # Now impose sum_k c_k = 0 to SOLVE for c0:
    # build with c0=0 contribution and c1 fixed; even-index chain from c0, odd from c1
    # c_even depends linearly on c0, c_odd on c1. sum = c0*Aeven + c1_part... 
    # Easier: even chain seeded by c0=1, sum_even ; odd chain seeded by c1, sum_odd
    ce=build_c(q,mp.mpf(1),mp.mpf(0))
    co=build_c(q,mp.mpf(0),c1)
    Se=sum(ce[k] for k in range(0,400,2))   # = c0-coefficient (with c0=1)
    So=sum(co[k] for k in range(1,400,2))
    # sum c_k = c0*Se + So = 0  => c0 = -So/Se
    c0_solved = -So/Se
    print(f"q={float(q):.2f} c1={mp.nstr(c1,8)} b0_closed={mp.nstr(b0c,12)} c0_from_L0=0 ={mp.nstr(c0_solved,12)} match={mp.nstr(abs(b0c-c0_solved),3)}")
