# Independent check: exact BFS on the stratum group, translation census by depth.
exec(open("stratum_fields.py").read().split("def wm_form(")[0])
import sys, time
m=int(sys.argv[1]); D=int(sys.argv[2]); legs=(int(sys.argv[3]),int(sys.argv[4]))
GS,IDS,K=gens_strat(m,*legs)
t0=time.time()
front=[IDS]; seen={IDS:0}; cen={}
for d in range(1,D+1):
    nf=[]; ntr=0
    for A in front:
        for i in range(3):
            N=mul(A,GS[i])
            if N in seen: continue
            seen[N]=d; nf.append(N)
            if (N[0]==K.const(1) and N[1]==K.const(0)
                and N[2]==K.const(0) and N[3]==K.const(1)): ntr+=1
    front=nf; cen[d]=ntr
    print(f"  m={m} legs{legs} d={d:2d}: layer {len(nf):6d} translations {ntr:5d} "
          f"[{time.time()-t0:.0f}s]", flush=True)
print(f"RESULT m={m} legs{legs} translation census: "
      f"{ {d:c for d,c in cen.items() if c} }")
