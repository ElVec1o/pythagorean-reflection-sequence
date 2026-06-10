# VERIFY the non-universality witness.
# Claim: for legs (a,b), the word  w = tau^c (xh) tau^|e'| (xh) tau^c (hxhx)
# with Phi_T = c t^2 + e' t + c  (primitive min poly of zeta_T) -- using
# tau = (xyh)^2 = translation 2(t^-1 - 1), r tau r^-1 = 2t(t^-1-1) --
# satisfies rho_T(w) = IDENTITY while w != 1 in the symbolic group.
from fractions import Fraction as F

def gauss(re_n, re_d, im_n, im_d): return (F(re_n,re_d), F(im_n,im_d))
def gmul(u,v): return (u[0]*v[0]-u[1]*v[1], u[0]*v[1]+u[1]*v[0])
def gadd(u,v): return (u[0]+v[0], u[1]+v[1])
def gsub(u,v): return (u[0]-v[0], u[1]-v[1])
def gconj(u): return (u[0],-u[1])
def ginv(u):
    n=u[0]*u[0]+u[1]*u[1]; return (u[0]/n, -u[1]/n)

def make_maps(a,b):
    # scaled coords; zeta=(a+bi)/(a-bi)
    z1=(F(a),F(b)); z2=(F(a),F(-b))
    zeta=gmul(z1,ginv(z2)); zinv=ginv(zeta)
    one=(F(1),F(0))
    # each map: z -> A*z + B*conj(z) + C   (affine over Q(i))
    X=( (F(0),F(0)), one, (F(0),F(0)) )                       # conj
    Y=( (F(0),F(0)), (F(-1),F(0)), (F(0),F(0)) )              # -conj
    H=( (F(0),F(0)), zinv, gsub(one,zinv) )                   # zeta^-1 conj + 1 - zeta^-1
    return {'x':X,'y':Y,'h':H}, zeta

def compose(f,g):
    # (f o g)(z) = f(g(z)); maps as (A,B,C): z -> A z + B conj z + C
    A1,B1,C1=f; A2,B2,C2=g
    A = gadd(gmul(A1,A2), gmul(B1,gconj(B2)))
    B = gadd(gmul(A1,B2), gmul(B1,gconj(A2)))
    C = gadd(gadd(gmul(A1,C2), gmul(B1,gconj(C2))), C1)
    return (A,B,C)

def word_map(letters, M):
    cur=( (F(1),F(0)), (F(0),F(0)), (F(0),F(0)) )  # identity
    for L in reversed(letters):   # rightmost applied first
        cur=compose(M[L],cur)
    return cur

def witness(a,b,c,e_abs,e_sign):
    # Phi_T = c t^2 + e' t + c ; we need translation 2(t^-1-1)*(c + e'*t + c*t^2)
    # tau^m: m copies (m>0) ; for negative coefficient use inverse of tau
    tau=['x','y','h','x','y','h']
    tau_inv=list(reversed(tau))   # all letters are involutions
    r=['x','h']; rinv=['h','x']
    def tpow(m): return (tau if m>0 else tau_inv)*abs(m)
    m0, m1, m2 = c, e_sign*e_abs, c
    w = tpow(m0) + r + tpow(m1) + r + tpow(m2) + rinv + rinv
    return w

for (a,b) in [(1,2),(3,4),(1,3)]:
    M,zeta=make_maps(a,b)
    # primitive min poly Phi = c t^2 - e t + c ; compute c,e
    s=a*a+b*b
    if (a%2==1 and b%2==1): c=s//2; e=(a*a-b*b)      # both odd
    else: c=s; e=2*(a*a-b*b)
    # Phi(t) = c t^2 - e t + c ; check Phi(zeta)=0
    val=gadd(gadd(gmul((F(c),F(0)),gmul(zeta,zeta)), gmul((F(-e),F(0)),zeta)), (F(c),F(0)))
    assert val==(0,0), (a,b,"Phi root check failed")
    w=witness(a,b,c,abs(e),-1 if e>0 else 1)   # coefficient of t is -e
    fm=word_map(w,M)
    ident=( (F(1),F(0)), (F(0),F(0)), (F(0),F(0)) )
    print(f"legs ({a},{b}): c={c}, e={e}, word length {len(w)}, rho_T(w)==identity: {fm==ident}")

# symbolic check: same word is NOT identity in the symbolic group
import sys
sys.path.insert(0,'/tmp/zeta_probe')
exec(open('/tmp/zeta_probe/probe.py').read().split("maxd=int")[0])
SG={'x':(1,1,0,{}), 'y':(-1,1,0,{}), 'h':(1,1,-1,{0:1,-1:-1})}
def sym_word(letters):
    cur=(1,0,0,{})
    for L in reversed(letters):
        cur=compose(SG[L],cur)
    return cur
# (1,2): c=5,e=-6 -> coeff of t = +6
w12=witness(1,2,5,6,1)
sw=sym_word(w12)
print("symbolic (1,2) witness: linear part",(sw[0],sw[1],sw[2]),"translation poly",sorted(sw[3].items()))
