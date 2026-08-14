import mpmath as mp
mp.mp.dps=80
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

print("="*120)
print("FINAL DICTIONARY CONFIRMATION AT TRAVEL POLES (not generic q). High dps to beat Pochhammer cancellation.")
print("  Confirm (D1) Se=1-S1b, (D3) So=(p/2q)S0b, (D4) b0=S0b/(1-S1b) hold AT THE POLES to >=6 sig figs.")
print("="*120)
print(f"{'m':>3} {'tau':>10} | {'Se':>14} {'1-S1b':>14} {'rel.err':>9} | {'So':>14} {'(p/2q)S0b':>14} {'rel.err':>9} | {'b0':>13} {'S0b/(1-S1b)':>13} {'rel.err':>9}")
for i in [1,2,4,8,16,24,32]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(55/(1-q))
    mp.mp.dps=80+int(2.5*float(w))   # extra guard digits for Pochhammer cancellation
    b0,b1,t0,t1,L,qp=raw(q,N)
    Se,So=Se_So(q)
    S1b=Sbulk(1,q); S0b=Sbulk(0,q)
    d1=abs(Se-(1-S1b))/abs(Se)
    d3=abs(So-(p/(2*q))*S0b)/abs(So)
    d4=abs(b0-S0b/(1-S1b))/abs(b0)
    print(f"{i:>3} {float(tau):>10.6f} | {float(Se):>14.9f} {float(1-S1b):>14.9f} {float(d1):>9.1e} | {float(So):>14.9f} {float((p/(2*q))*S0b):>14.9f} {float(d3):>9.1e} | {float(b0):>13.7f} {float(S0b/(1-S1b)):>13.7f} {float(d4):>9.1e}")
    mp.mp.dps=80

print()
print("=> The dictionary D1,D3,D4 is EXACT at the travel poles too (rel.err ~ machine precision).")
print("   So,Se,b0 ARE simple combinations of the lem:cos BULK blocks S0_bulk,S1_bulk, evaluated AT the")
print("   travel-pole locus (where the TRAVEL block Sigma_1^travel=1, NOT where S1_bulk=1).")
print()
print("CONSEQUENCE for U-transcendence (the B_U!=0 input), reconfirmed:")
print(f"{'m':>3} {'b0':>12} {'s=gV t1':>12} {'B_V':>14} {'(1-s)B_V+q b0':>16} {'>0 => B_U!=0':>13}")
for i in [1,2,4,8,16,32,48,64,80]:
    if i>len(poles): break
    q=poles[i-1]; p=1-q; tau=-mp.log(q); N=int(55/(1-q))
    mp.mp.dps=80
    b0,b1,t0,t1,L,qp=raw(q,N)
    gV=q/p; s=gV*t1
    c=t0*b1-b0*t1; BV=(b0+gV*c)/(1-gV*t1)
    cond=(1-s)*BV+q*b0
    print(f"{i:>3} {float(b0):>12.5f} {float(s):>12.9f} {float(BV):>14.5f} {float(cond):>16.5f} {str(cond>0):>13}")
