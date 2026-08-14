import math
def raw_f(q,N):
    qp=[1.0]*(N+1)
    for b in range(1,N+1): qp[b]=qp[b-1]*q
    v=[0.0]*(N+1); u0=[0.0]*(N+1); u1=[0.0]*(N+1)
    for b in range(N,0,-1):
        qb=qp[b]; q2b=qb*qb; q3b=q2b*qb; dd=1-2*q2b-2*qb*v[b]
        vb=(v[b]*(1+2*q2b)+2*q3b)/dd; c0=2*qb; c1=2*q2b
        u0[b-1]=u0[b]*(1+2*q2b)+qb*c0+vb*(c0+2*qb*u0[b])
        u1[b-1]=u1[b]*(1+2*q2b)+qb*c1+vb*(c1+2*qb*u1[b]); v[b-1]=vb
    l0=0.0; L=[0.0]
    for b in range(1,N+1):
        qb=qp[b]; q2b=qb*qb; dd=1-2*q2b-2*qb*v[b]
        l0=(l0+2*qb+2*qb*u0[b])/dd; L.append(l0)
    return l0,L
poles=[float(l.split()[-1]) for l in open('poles.txt') if l.split()]

# S_c = (1-q) sum_{a>=c} q^a L_a. Is S_c oscillatory? max|S_c| scale?
m=8; q=poles[m-1]; N=int(50/(1-q)); tau=-math.log(q); w=math.sqrt(2/tau)
b0,L=raw_f(q,N)
acc=0.0; S=[0.0]*(N+1)
for a in range(N-1,0,-1):
    acc+=q**a*L[a]; S[a]=(1-q)*acc
print(f'm={m} w={w:.3f}  max|S|={max(abs(x) for x in S):.4f}  ~w/? : w={w:.2f}')
# S vs continuum: S(u)=(b0/(w sin w))(cos(w(1-u))-cos w) from before. At u=q^c.
# Sigma=sum S_c q^{c-1}. Let's verify Sigma->1/2 via direct continuum of S with CORRECT b0~2/tau.
# S_c ~ (b0/(w sin w))(cos(w(1-q^c))-cos w). Sigma=(1/q)sum S_c q^c ~(1/(q tau))int_0^1 S(u)du.
# int_0^1 S(u)du=(b0/(w sin w))(sin w/w - cos w). With cos w->0,sin w=+-1 at pole:
#   = (b0/(w*(+-1)))(( +-1)/w - 0)= b0/w^2. b0~2/tau, w^2=2/tau => b0/w^2->1.
# Sigma~(1/(q tau))*(b0/w^2)?? that has extra 1/tau. WRONG dimension again -> the sin-form S is off.
# Print the pieces:
import math as M
b0v=b0; cw=M.cos(w); sw=M.sin(w)
intS=(b0v/(w*sw))*(sw/w - cw)
print(f'  continuum int_0^1 S du (sin-form) = {intS:.5f}, /(q tau)= {intS/(q*tau):.5f}  (TRUE Sigma~0.5)')
print(f'  b0/w^2={b0v/w**2:.5f}  cos w={cw:.5f} sin w={sw:.5f}')
