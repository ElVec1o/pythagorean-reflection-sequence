#!/usr/bin/env python3
"""
c_mine.py -- harvest the connectivity penalty c = (true - relaxed)/2 for EVERY element
in the ball up to depth D, with full structural decode, to reverse-engineer the exact
closed form for c (the only missing piece of a closed-form geodesic length).

true length  = lamp_lib.bfs distance (exact, connected geodesic).
relaxed      = catalytic_funceq.relaxed_len_local (exact relaxed, closed form, <= true).
"""
import sys, os, importlib.util
import lamp_lib as LL

HERE=os.path.dirname(os.path.abspath(__file__))
def load(mod, path):
    sv=list(sys.argv); spec=importlib.util.spec_from_file_location(mod, os.path.join(HERE,path))
    m=importlib.util.module_from_spec(spec); sys.argv=[mod,"0"]; spec.loader.exec_module(m); sys.argv=sv
    return m
cf=load("cf","catalytic_funceq.py")
relaxed_len=cf.relaxed_len_local

def f_of(j,k): return 1 if 0<=j<k else (-1 if k<=j<0 else 0)

def structure(eps,dl,k,a):
    """Return a structural summary used to model c."""
    a={j:v for j,v in a.items() if v!=0}
    nz=sorted(a)
    trav=list(range(0,k)) if k>0 else (list(range(k,0)) if k<0 else [])
    vsites={0,k}
    for j in nz:   vsites|={j,j+1}
    for j in trav: vsites|={j,j+1}
    lo=min(vsites); hi=max(vsites)
    # active edge = deposit or travel; gap edge = neither, inside [lo,hi)
    active=set(j for j in range(lo,hi) if a.get(j,0)!=0 or f_of(j,k)!=0)
    gaps=[j for j in range(lo,hi) if j not in active]
    # group gaps into maximal runs
    runs=[]
    for j in gaps:
        if runs and runs[-1][-1]==j-1: runs[-1].append(j)
        else: runs.append([j])
    # classify each run by what bounds it (left edge j-1's right end = site j; etc.)
    run_info=[]
    for r in runs:
        L=r[0]; R=r[-1]
        leftsite=L; rightsite=R+1            # run occupies edges L..R -> sites L..R+1
        # what is immediately left (site leftsite) / right (site rightsite)?
        # neighbor active edge on left is edge L-1, on right is edge R+1
        left_active = (a.get(L-1,0)!=0 or f_of(L-1,k)!=0)
        right_active= (a.get(R+1,0)!=0 or f_of(R+1,k)!=0)
        # is a marker site (0 or k) at the run's boundary?
        marker_left = leftsite in (0,k)
        marker_right= rightsite in (0,k)
        run_info.append(dict(edges=r,length=len(r),Lsite=leftsite,Rsite=rightsite,
                             left_active=left_active,right_active=right_active,
                             marker_left=marker_left,marker_right=marker_right))
    return dict(lo=lo,hi=hi,nz=nz,trav=trav,k=k,runs=run_info,a=a,eps=eps,dl=dl)

def main():
    D=int(sys.argv[1]) if len(sys.argv)>1 else 12
    dist=LL.bfs(D)
    rows=[]; bad=0; odd=0
    for (e,dl,k,L),d in dist.items():
        a=dict(L)
        r=relaxed_len(e,dl,k,a)
        if r is None: bad+=1; continue
        diff=d-r
        if diff<0:
            print("!! relaxed > true:",(e,dl,k,a),"rel",r,"true",d); continue
        if diff%2: odd+=1
        c=diff//2
        rows.append((c,e,dl,k,a,r,d))
    print(f"# depth {D}: {len(rows)} elts, {bad} infeasible-relaxed, {odd} ODD diffs (should be 0)")
    from collections import Counter
    print("# c distribution:", dict(sorted(Counter(c for c,*_ in rows).items())))
    # show all c>0 with structure, sorted by (c, true len)
    pos=[row for row in rows if row[0]>0]
    pos.sort(key=lambda r:(r[0],r[6],r[3]))
    print(f"# {len(pos)} elements with c>0. First 60:")
    for c,e,dl,k,a,r,d in pos[:60]:
        st=structure(e,dl,k,a)
        runs=[(ri['length'],'mL' if ri['marker_left'] else '.','mR' if ri['marker_right'] else '.',
               'aL' if ri['left_active'] else '_','aR' if ri['right_active'] else '_') for ri in st['runs']]
        print(f"  c={c} e={e:+d} dl={dl} k={k:+d} a={a} rel={r} true={d} | runs(len,mL,mR,aL,aR)={runs}")
    return rows

if __name__=="__main__":
    main()
