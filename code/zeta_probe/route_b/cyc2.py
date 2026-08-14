import sys
from collections import defaultdict, Counter
import lamp_lib as LL

maxd=int(sys.argv[1]) if len(sys.argv)>1 else 13
dist=LL.bfs(maxd)
vN=defaultdict(int); uN=defaultdict(int)
cyc=[]
for (e,dl,k,L),d in dist.items():
    tl=LL.solve(e,dl,k,L)
    rl=LL.relaxed_solve(e,dl,k,L)
    if tl is None or rl is None: continue
    if tl!=d:
        print("TRUE MISMATCH",(e,dl,k,dict(L)),d,tl); continue
    uN[tl]+=1; vN[rl]+=1
    if tl>rl:
        cyc.append((rl,tl,(tl-rl)//2,e,dl,k,dict(L)))
u=[uN[n] for n in range(maxd+1)]
v=[vN[n] for n in range(maxd+1)]
dd=[v[n]-u[n] for n in range(maxd+1)]
ref_u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203]
ref_v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513]
print("u_n=",u)
print("v_n=",v)
print("d_n=",dd)
print("u OK:", all(u[n]==ref_u[n] for n in range(min(len(u),len(ref_u)))))
print("v OK:", all(v[n]==ref_v[n] for n in range(min(len(v),len(ref_v)))))
cyc.sort()
print(f"# cycle elements (c>=1) up to len {maxd}: {len(cyc)}")
for rl,tl,c,e,dl,k,L in cyc[:30]:
    print(f"  rl={rl} tl={tl} c={c} eps={e} dl={dl} k={k} a={L}")
print("c distribution:", dict(Counter(x[2] for x in cyc)))
print("relaxed_len of cycle elts:", dict(sorted(Counter(x[0] for x in cyc).items())))
print("k of cycle elts:", dict(sorted(Counter(x[5] for x in cyc).items())))
