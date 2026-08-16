from collections import deque
import sys
def rf(n):  # Gamma_n edges: |i-j|>=2
    return {(i,j) for i in range(n+1) for j in range(n+1) if i<j and abs(i-j)>=2}
def make(E,N):
    adj=lambda i,j: (min(i,j),max(i,j)) in E
    def reduce_w(w):
        ch=True
        while ch:
            ch=False
            for i in range(len(w)):
                for j in range(i+1,len(w)):
                    if w[i]==w[j] and all(adj(int(w[i]),int(w[k])) for k in range(i+1,j)):
                        w=w[:i]+w[i+1:j]+w[j+1:]; ch=True; break
                if ch: break
        return w
    def canon(w):
        seen={w}; q=deque([w]); best=w
        while q:
            x=q.popleft()
            if x<best: best=x
            for i in range(len(x)-1):
                if x[i]!=x[i+1] and adj(int(x[i]),int(x[i+1])):
                    y=x[:i]+x[i+1]+x[i]+x[i+2:]
                    if y not in seen: seen.add(y); q.append(y)
        return best
    return lambda w: canon(reduce_w(w))
n=int(sys.argv[1]); D=int(sys.argv[2])
E=rf(n); N=n+1
nf=make(E,N)
# quotients: add each consecutive-pair edge
quos=[]
for i in range(n):
    quos.append(make(E|{(i,i+1)},N))
print(f"n={n}: W_n spheres vs image in the product over adding each consecutive edge")
front=[""]; seen={""}; simg={nf("")}
tot_w=1; tot_i=1
for d in range(1,D+1):
    nxt=[]; imgs=set()
    for w in front:
        for g in range(N):
            x=nf(w+str(g))
            if len(x)!=d or x in seen: continue
            seen.add(x); nxt.append(x)
            imgs.add(tuple(q(x) for q in quos))
    front=nxt
    print(f"   d={d:2d}:  |W_n sphere| = {len(nxt):6d}   |image sphere| = {len(imgs):6d}   {'OK' if len(nxt)==len(imgs) else 'COLLAPSE'}")
    if len(nxt)!=len(imgs): break
