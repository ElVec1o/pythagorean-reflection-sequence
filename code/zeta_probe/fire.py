# FIRE: compute u_0..u_D from the THEORY ALONE (normal form + metric formula),
# with no group BFS anywhere, and compare to published A396406.
# Elements: (eps, delta, k, a) with parity normal form:
#   a_j odd  <=> j in [min(0,k), max(0,k))   (travel edges)
# Enumerate all data with cost lower bound <= D; exact length by profile DP.
import sys, time
exec(open('lamp_profile.py').read().split("maxd=int")[0])

D=int(sys.argv[1]) if len(sys.argv)>1 else 16
PUB=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683]

def travel_range(k):
    if k>0: return 0,k     # edges 0..k-1
    if k<0: return k,0     # edges k..-1
    return 0,0             # empty

t0=time.time()
hist=[0]*(D+1)
count_checked=0
for k in range(-D,D+1):
    lo,hi=travel_range(k)
    trav=set(range(lo,hi))
    base_travel=len(trav)              # each travel edge needs m>=1
    if base_travel> D: continue
    # positions where a_j may be nonzero: window [k-D, D] roughly; bound by budget
    # enumerate a-vectors recursively over j from (min(lo,0)-(D)) .. (hi+D)
    JMIN=min(lo,0)-(D-base_travel)//2-1
    JMAX=hi+(D-base_travel)//2+1
    positions=list(range(JMIN,JMAX))
    # recursive enumeration with pruning
    def rec(idx, acc, budget_used):
        global count_checked
        if budget_used>D: return
        if idx==len(positions):
            # build dict, compute hull-gap extra cost lower bound quickly
            a={j:v for j,v in acc.items() if v!=0}
            # quick lower bound: sum m_j over hull (gaps cost 2) + |k|-1 passes
            nz=[j for j in a]
            hull=nz+list(trav)
            lb=0
            if hull:
                A=min(hull+[0]); B=max(hull+[-1])
                for j in range(A,B+1):
                    v=abs(a.get(j,0))
                    if v==0:
                        lb+= 2 if (j in trav or (A<=j<=B and any(jj< j for jj in hull) and any(jj> j for jj in hull))) and v==0 and (j not in trav) else (1 if j in trav else 0)
                        if j in trav: lb=lb  # travel odd => >=1 handled
                    else:
                        lb+=v
            if lb>D: return
            for eps in (1,-1):
                for dl in (0,1):
                    l=solve(eps,dl,k,freeze(a))
                    count_checked+=1
                    if l is not None and l<=D:
                        hist[int(l)]+=1
            return
        j=positions[idx]
        par = 1 if j in trav else 0
        # values with |v| parity par, budget: cost >= |v| (>=1 travel, >=2 even nz)
        vals=[]
        rem=D-budget_used
        if par==1:
            v=1
            while v<=rem:
                vals.append(v); vals.append(-v); v+=2
        else:
            vals.append(0)
            v=2
            while v<=rem:
                vals.append(v); vals.append(-v); v+=2
        for v in vals:
            cost=abs(v) if v!=0 else (1 if par==1 else 0)
            if par==1 and v==0: continue
            acc[j]=v
            rec(idx+1, acc, budget_used+ (abs(v) if v!=0 else 0) + (0))
            del acc[j]
    # budget accounting: travel edges contribute |v|>=1 inherently via vals
    rec(0,{},0)
print(f"[{time.time()-t0:.0f}s] candidates evaluated: {count_checked}")
print("computed:", hist)
print("published:", PUB[:D+1])
print("MATCH" if hist==PUB[:D+1] else "MISMATCH")
