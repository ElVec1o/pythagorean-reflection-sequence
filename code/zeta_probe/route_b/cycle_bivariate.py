# Bivariate connectivity DP: W(x,y) = sum_g x^{relaxed_len(g)} y^{c(g)}
# where c(g) = number of isolated cycles that must be spliced in.
# Then  V(x)=W(x,1)   (relaxed: cycles free),
#       U(x)=W(x,x^2) (true: each cycle costs +2 -> x^{len+2c}),
#       D(x)=V-U=W(x,1)-W(x,x^2).
# We track length as a polynomial in x (dict deg->poly in y as dict).
# A genuine isolated cycle = a component that closes (0 strands) with NO markers.
# A dangling marker (start XOR end, 0 strands) remains invalid.
# Based on lamp_profile.py solve(), but we ENUMERATE all words (count, with y per cycle),
# not minimize length. Length is exact relaxed length of that profile config.
#
# IMPORTANT: lamp_profile minimizes over m,pu (the crossing/pairing freedom) to get the
# GEODESIC. Here a group element is a fixed (eps,delta,k;a). Its relaxed length is the
# MIN over profiles; its true length is MIN over profiles WITH connectivity. The defect
# per element is (true_len - relaxed_len). To get d_n we need, per element g:
#   relaxed_len(g), and  c(g) := (true_len(g)-relaxed_len(g))/2  >= 0.
# So this is NOT a simple bivariate count; we must compute BOTH minima per element.
#
# Strategy: reuse the two existing exact solvers element-by-element over an enumeration
# of all elements with relaxed_len <= N, and tally d_n = #{g: true_len(g)=? } differences.
# But it's cleaner: u_n = #{g: true_len=n}, v_n=#{g: relaxed_len=n}. We enumerate ALL g
# with relaxed_len<=N, record (relaxed_len, true_len), then
#   v_n=#{relaxed_len=n}, u_n=#{true_len=n}, d_n=v_n-u_n.
# This directly tests the cycle interpretation against the known data.

import sys
sys.path.insert(0, '/Users/vico/Documents/elvec1o/XXXXX MATH PROOF/code/zeta_probe')
from lamp_profile import solve as true_solve, bfs

# relaxed solver: same DP but isolated cycles allowed (cost 0, not invalid)
from functools import lru_cache
from itertools import permutations

def pcost(a_side,a_sign,d_side,d_sign):
    if a_side!=d_side: return 1
    return 0 if a_sign==d_sign else 2

def relaxed_solve(eps_t, dl_t, k, a):
    # identical to lamp_profile.solve but isolated cycles (0 strands, no markers) are
    # ALLOWED at cost 0 (they just vanish). Dangling single marker still invalid.
    a=dict(a)
    nz=[j for j in a if a[j]!=0]
    if k>0: trav=list(range(0,k))
    elif k<0: trav=list(range(k,0))
    else: trav=[]
    hull=nz+trav
    if not hull:
        d_side = 'R' if dl_t==1 else 'L'
        d_sign = 1 if eps_t==1 else -1
        return pcost('L',1,d_side,d_sign)
    A=min(hull+[0]); B=max(hull+[-1])
    EXT=1
    edges=list(range(A-EXT,B+1+EXT))
    def f(j):
        if 0<=j<k: return 1
        if k<=j<0: return -1
        return 0
    INF=float('inf')
    init_state=( (), False, False )
    states={init_state:0}
    for j in edges:
        fj=f(j); aj=a.get(j,0)
        base=max(abs(aj),abs(fj))
        if (base-abs(aj))%2: base+=1
        cand=[]
        for lam in range(0,3):
            m=base+2*lam
            if m==0 and (aj!=0 or fj!=0): continue
            cand.append(m)
        nstates={}
        for (comps, sp, ep), c0 in states.items():
            if comps=='DONE':
                if 0 in cand and aj==0 and fj==0 and j!=0 and j!=k:
                    key=(comps,sp,ep)
                    if key not in nstates or c0<nstates[key]:
                        nstates[key]=c0
                continue
            for m in cand:
                u=(m+fj)//2; dn=(m-fj)//2
                if u<0 or dn<0: continue
                for pu in range(u+1):
                    t=aj+dn-u+2*pu
                    if t%2: continue
                    pd=t//2
                    if pd<0 or pd>dn: continue
                    prev_m=sum(cc[0]+cc[1]+cc[2]+cc[3] for cc in comps)
                    if j<=-1 and prev_m>0 and m==0: continue
                    if j>=1 and prev_m==0 and m>0: continue
                    arr=[]; dep=[]
                    for ci,cc in enumerate(comps):
                        for _ in range(cc[0]): arr.append(('L',1,('old',ci)))
                        for _ in range(cc[1]): arr.append(('L',-1,('old',ci)))
                        for _ in range(cc[2]): dep.append(('L',1,('old',ci)))
                        for _ in range(cc[3]): dep.append(('L',-1,('old',ci)))
                    newrefs=[]; nid=0
                    for _ in range(pd): arr.append(('R',1,('new',nid))); newrefs.append(('dn',1)); nid+=1
                    for _ in range(dn-pd): arr.append(('R',-1,('new',nid))); newrefs.append(('dn',-1)); nid+=1
                    for _ in range(pu): dep.append(('R',1,('new',nid))); newrefs.append(('up',1)); nid+=1
                    for _ in range(u-pu): dep.append(('R',-1,('new',nid))); newrefs.append(('up',-1)); nid+=1
                    if j==0: arr.append(('L',1,('start',0)))
                    if j==k:
                        dep.append(('R' if dl_t==1 else 'L', 1 if eps_t==1 else -1, ('end',0)))
                    if len(arr)!=len(dep): continue
                    n=len(arr)
                    if n==0:
                        if m!=0: continue
                        ok=True
                        for cc in comps:
                            if cc[0]+cc[1]+cc[2]+cc[3]>0: ok=False
                        if not ok: continue
                        key=(comps,sp,ep)
                        if key not in nstates or c0<nstates[key]:
                            nstates[key]=c0
                        continue
                    base_cost=c0+m
                    seen_pair=set()
                    for perm in permutations(range(n)):
                        sigkey=tuple((arr[i][0],arr[i][1],arr[i][2],dep[perm[i]][0],dep[perm[i]][1],dep[perm[i]][2]) for i in range(n))
                        sigkey=tuple(sorted(sigkey))
                        if sigkey in seen_pair: continue
                        seen_pair.add(sigkey)
                        cost=base_cost
                        parent={}
                        def find(z):
                            while parent.get(z,z)!=z:
                                parent[z]=parent.get(parent[z],parent[z]); z=parent[z]
                            return z
                        def union(p,q):
                            rp,rq=find(p),find(q)
                            if rp!=rq: parent[rp]=rq
                        for ci in range(len(comps)): parent[('old',ci)]=('old',ci)
                        for ni in range(nid): parent[('new',ni)]=('new',ni)
                        parent[('start',0)]=('start',0); parent[('end',0)]=('end',0)
                        ok=True
                        for i in range(n):
                            a_s,a_g,a_ref=arr[i]; d_s,d_g,d_ref=dep[perm[i]]
                            cost+=pcost(a_s,a_g,d_s,d_g)
                            union(a_ref,d_ref)
                        groups={}
                        for ni in range(nid):
                            groups.setdefault(find(('new',ni)),[0,0,0,0,False,False])
                            kind,sg=newrefs[ni]
                            idx = (0 if sg==1 else 1) if kind=='up' else (2 if sg==1 else 3)
                            groups[find(('new',ni))][idx]+=1
                        for ci,cc in enumerate(comps):
                            r=find(('old',ci))
                            groups.setdefault(r,[0,0,0,0,False,False])
                            if cc[4]: groups[r][4]=True
                            if cc[5]: groups[r][5]=True
                        if j==0:
                            r=find(('start',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][4]=True
                        if j==k:
                            r=find(('end',0)); groups.setdefault(r,[0,0,0,0,False,False]); groups[r][5]=True
                        newcomps=[]; finished=None
                        for r,g in groups.items():
                            ns=g[0]+g[1]+g[2]+g[3]
                            if ns==0:
                                if g[4] and g[5]:
                                    if finished is not None: ok=False; break
                                    finished=g
                                elif g[4] or g[5]:
                                    ok=False; break   # dangling single marker: still invalid
                                else:
                                    # isolated cycle: RELAXED allows it for free, just drop
                                    pass
                            else:
                                newcomps.append(tuple(g))
                        if not ok: continue
                        if finished is not None and newcomps:
                            continue
                        nsp = sp or (j==0); nep = ep or (j==k)
                        if finished is not None:
                            key=('DONE', nsp, nep)
                        else:
                            key=(tuple(sorted(newcomps)), nsp, nep)
                        if key not in nstates or cost<nstates[key]:
                            nstates[key]=cost
        states=nstates
        if not states: return None
    best=INF
    for key,c in states.items():
        if key[0]=='DONE' and key[1] and key[2]:
            best=min(best,c)
    return None if best==INF else best

if __name__=="__main__":
    maxd=int(sys.argv[1]) if len(sys.argv)>1 else 12
    dist=bfs(maxd)
    from collections import defaultdict
    vN=defaultdict(int); uN=defaultdict(int)
    relok=0; relmis=0
    for (e,dl,k,L),d in dist.items():
        tl=true_solve(e,dl,k,L)
        rl=relaxed_solve(e,dl,k,L)
        # d is the TRUE bfs distance; tl should equal d
        if tl!=d:
            print("TRUE MISMATCH", (e,dl,k,dict(L)), d, tl); continue
        if rl is None or rl>tl:
            print("REL BAD", (e,dl,k,dict(L)), "tl",tl,"rl",rl); continue
        uN[tl]+=1
        vN[rl]+=1
    N=maxd
    u=[uN[n] for n in range(N+1)]
    v=[vN[n] for n in range(N+1)]
    dd=[v[n]-u[n] for n in range(N+1)]
    print("u_n=",u)
    print("v_n=",v)
    print("d_n=",dd)
    ref_u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345]
    ref_v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451]
    print("u matches:", all(u[n]==ref_u[n] for n in range(min(len(u),len(ref_u)))))
    print("v matches:", all(v[n]==ref_v[n] for n in range(min(len(v),len(ref_v)))))
