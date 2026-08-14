#!/usr/bin/env python3
"""
TASK C - IBP control integral, FAST: sample A(y),Phi(y) once on a fine grid,
get Phi' by finite differences, F=A/Phi', then I = sum |Delta F| (total variation
of F = int |F'| dy). Study cutoff dependence Y -> pole pi/tau.
Print progressively (flush) so we can watch.
"""
import sys
import mpmath as mp
from taskC_Bs import B_s
mp.mp.dps = 30

tau = mp.mpf('0.01')
w = mp.sqrt(2/tau); W = w*mp.e**(-tau/2); ystar = W/2
POLE = mp.pi/tau
KMAX, PMAX = 80, 16

def sample(y):
    y = mp.mpf(y)
    B = B_s(mp.mpc(0,1)*y, tau, Kmax=KMAX, Pmax=PMAX)
    g = 1 - mp.e**(-B)
    Aval = abs(g)*mp.sqrt(mp.coth(mp.pi*y)/(mp.pi*y))
    Phival = 2*y*mp.log(W) + mp.im(mp.log(g)) - mp.im(mp.loggamma(1+2*mp.mpc(0,1)*y))
    return Aval, Phival

# Build a fine grid from 0.3 to 312 (just below pole), denser near y* and near pole.
def build_grid():
    g = []
    # 0.3..(y*-1) step 0.1 ; skip [y*-1,y*+1] ; (y*+1)..50 step 0.25 ; 50..312 step 0.5
    y = mp.mpf('0.3')
    while y <= ystar-1+mp.mpf('1e-9'):
        g.append(y); y += mp.mpf('0.1')
    y = ystar+1
    while y <= 50:
        g.append(y); y += mp.mpf('0.25')
    while y <= 312:
        g.append(y); y += mp.mpf('0.5')
    return g

if __name__ == "__main__":
    grid = build_grid()
    print(f"tau={tau} y*={mp.nstr(ystar,7)} pole={mp.nstr(POLE,7)}  Ngrid={len(grid)}", flush=True)
    # sample
    As=[]; Phis=[]
    for i,y in enumerate(grid):
        a,p = sample(y); As.append(a); Phis.append(p)
        if i % 100 == 0:
            print(f"  sampled {i}/{len(grid)} y={mp.nstr(y,5)}", flush=True)
    # Phi' by central differences on the grid
    Phip=[None]*len(grid)
    for i in range(len(grid)):
        if i==0: Phip[i]=(Phis[1]-Phis[0])/(grid[1]-grid[0])
        elif i==len(grid)-1: Phip[i]=(Phis[-1]-Phis[-2])/(grid[-1]-grid[-2])
        else: Phip[i]=(Phis[i+1]-Phis[i-1])/(grid[i+1]-grid[i-1])
    # F = A/Phi'
    F=[As[i]/Phip[i] for i in range(len(grid))]
    # total variation int|F'| in cutoff windows. Left = grid<y*; right = grid>y* up to Ycut.
    # all grid points already satisfy |y-y*|>=1.
    iy = next(i for i,y in enumerate(grid) if y>ystar)  # first index right of y*
    # left TV over [0.3, y*-1]:
    leftTV = sum(abs(F[i+1]-F[i]) for i in range(0,iy-1))
    print(f"\nleft TV (int|F'|, [0.3,y*-1]) = {mp.nstr(leftTV,7)}", flush=True)
    print("right TV [y*+1,Ycut] vs cutoff:", flush=True)
    for Yc in [15,30,60,100,150,200,250,290,300,310]:
        rt = sum(abs(F[i+1]-F[i]) for i in range(iy, len(grid)-1) if grid[i+1]<=Yc)
        print(f"   Ycut={Yc:>4}: rightTV={mp.nstr(rt,7)}   I_total={mp.nstr(leftTV+rt,7)}", flush=True)
    # also report sup A excluding pole region and A at y*
    supA=max(As[:next(i for i,y in enumerate(grid) if y>300)]);
    iA=As.index(supA)
    print(f"\nsup A on grid (y<=300) = {mp.nstr(supA,7)} at y={mp.nstr(grid[iA],6)}", flush=True)
    iystar=min(range(len(grid)),key=lambda i:abs(grid[i]-ystar))
    print(f"A(y*+1~{mp.nstr(grid[iy],5)}) = {mp.nstr(As[iy],6)}", flush=True)
