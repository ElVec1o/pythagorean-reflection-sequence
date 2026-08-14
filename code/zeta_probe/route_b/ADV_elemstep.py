import mpmath as mp
mp.mp.dps=50
print("Elementary-step audit of P12 leading order E=(1/2)(w-W)^2 sinw sin(w-W):")
print(f"{'tau':>10} {'(w-W)/sqrt(tau/2)':>18} {'(1/2)(w-W)^2/(tau/4)':>22} {'sin(w-W)/(w-W)':>16} {'E/(sinw t^1.5/4sqrt2)':>22}")
for taue in ['1e-2','1e-3','1e-4','1e-5','1e-6']:
    tau=mp.mpf(taue); w=mp.sqrt(2/tau); W=w*mp.e**(-tau/2); sw=mp.sin(w)
    dwW=w-W
    a=dwW/mp.sqrt(tau/2)
    b=(mp.mpf(1)/2*dwW**2)/(tau/4)
    c=mp.sin(dwW)/dwW
    E=mp.mpf(1)/2*dwW**2*sw*mp.sin(dwW)
    pred=sw*tau**mp.mpf('1.5')/(4*mp.sqrt(2))
    print(f"{float(tau):>10.1e} {float(a):>18.10f} {float(b):>22.12f} {float(c):>16.10f} {float(E/pred):>22.12f}")
print("All -> 1: E IS the elementary leading term sinw tau^1.5/(4sqrt2), NO saddle constant.")
