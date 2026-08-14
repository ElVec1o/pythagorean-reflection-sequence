import sys, os
from collections import defaultdict, Counter
import lamp_lib as LL
import importlib.util
maxd=int(sys.argv[1]) if len(sys.argv)>1 else 14
HERE=os.path.dirname(os.path.abspath(__file__))
_save=list(sys.argv)
spec=importlib.util.spec_from_file_location("cf", os.path.join(HERE,"catalytic_funceq.py"))
cf=importlib.util.module_from_spec(spec); sys.argv=["cf","0"]; spec.loader.exec_module(cf); sys.argv=_save
relaxed_len=cf.relaxed_len_local

# BFS true distance to a generous radius (relaxed<=true, so to capture all elements with
# relaxed_len<=maxd we need radius where their TRUE len lies; true len can exceed relaxed by 2c.
# Cap radius at maxd+ slack. Use radius = maxd + 8 (defect grows but per-element c is small at low len).
RAD=maxd+8
dist=LL.bfs(RAD)
vN=defaultdict(int); uN=defaultdict(int)
cyc=[]
seen=set()
for (e,dl,k,L),tl in dist.items():
    rl=relaxed_len(e,dl,k,L)
    if rl is None: continue
    if rl>tl:
        print("REL>TRUE BUG",(e,dl,k,dict(L)),"rl",rl,"tl",tl); continue
    if tl<=maxd: uN[tl]+=1
    if rl<=maxd: vN[rl]+=1
    if tl>rl and rl<=maxd:
        cyc.append((rl,tl,(tl-rl)//2,e,dl,k,dict(L)))
u=[uN[n] for n in range(maxd+1)]
v=[vN[n] for n in range(maxd+1)]
dd=[v[n]-u[n] for n in range(maxd+1)]
ref_u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574]
ref_v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418]
print("u_n=",u)
print("v_n=",v)
print("d_n=",dd)
print("u OK:", all(u[n]==ref_u[n] for n in range(min(len(u),len(ref_u)))))
print("v OK:", all(v[n]==ref_v[n] for n in range(min(len(v),len(ref_v)))))
cyc.sort(key=lambda t:(t[0],t[1],t[2],t[3],t[4],t[5]))
print(f"# cycle elements (c>=1) with relaxed_len<= {maxd}: {len(cyc)}")
for rl,tl,c,e,dl,k,L in cyc:
    print(f"  rl={rl} tl={tl} c={c} eps={e} dl={dl} k={k} a={L}")
print("c distribution:", dict(sorted(Counter(x[2] for x in cyc).items())))
print("relaxed_len of cycle elts:", dict(sorted(Counter(x[0] for x in cyc).items())))
print("k of cycle elts:", dict(sorted(Counter(x[5] for x in cyc).items())))
print("abs(k) of cycle elts:", dict(sorted(Counter(abs(x[5]) for x in cyc).items())))
