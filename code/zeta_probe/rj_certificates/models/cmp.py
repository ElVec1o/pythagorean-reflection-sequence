import sys, numpy as np
D=int(sys.argv[1]); M=np.load(sys.argv[2]); f=sys.argv[3]
B={}
for l in open(f):
    if l.startswith('BIV'):
        _,a,c,sg,v=l.split(); B[(int(a),int(c),int(sg))]=int(v)
nck=0; bad=[]; tot=[0,0,0]; maxc=0
for sg in (-1,0,1):
    top = D if sg==0 else D-1
    for n in range(0,min(top,int(sys.argv[4]))+1):
        for c in range(0,n//2+1):
            a=n-2*c; t=B.get((a,c,sg),0); m=int(M[sg+1][n,c]) if c<M.shape[2] else 0
            nck+=1; tot[sg+1]+=t
            if t!=m: bad.append((sg,a,c,t,m))
print('checked coefficients',nck,'elements covered per sector',tot,'mismatches',len(bad)); print(bad[:20])
