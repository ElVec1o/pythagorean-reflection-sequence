# dround.py -- directed-rounding decimal printing of Arb balls (P1f, fix of Reviewer AA gap 2).
# fdn(x, d): a decimal string <= every point of the ball x (lower bound rounded DOWN to d significant digits).
# fup(x, d): a decimal string >= every point of the ball x (upper bound rounded UP to d significant digits).
# The decimal strings are exact (integer mantissa + exponent); the float conversion of the Arb endpoint is
# pushed one ulp outward and the mantissa is floored/ceiled after a further relative 1e-12 outward nudge,
# which dominates all double-precision rounding in the scaling step.
import math
from flint import arb
def _fmt(m, e):
    s = str(abs(m)); sign = '-' if m < 0 else ''
    if m == 0: return '0'
    # value = m * 10^e ; print as mantissa with decimal point
    k = len(s) - 1; ee = e + k
    mant = s[0] + ('.' + s[1:] if len(s) > 1 else '')
    if -4 <= ee <= 5:
        from decimal import Decimal
        return sign + format(Decimal(s).scaleb(e), 'f')
    return '%s%se%+d' % (sign, mant, ee)
def fdn(x, d=4):
    if not isinstance(x, arb): x = arb(x)
    if not x.is_finite(): return '-inf'
    v0 = float(x.lower())
    if v0 == 0 and bool(x.lower() == 0): return '0'
    v = math.nextafter(v0, -math.inf)
    if abs(v) < 1e-300: return '-1e-300'
    e = math.floor(math.log10(abs(v))) - (d - 1)
    y = v*(1 - 1e-12) if v > 0 else v*(1 + 1e-12)
    m = math.floor(y/10.0**e)
    return _fmt(m, e)
def fup(x, d=4):
    if not isinstance(x, arb): x = arb(x)
    if not x.is_finite(): return 'inf'
    v0 = float(x.upper())
    if v0 == 0 and bool(x.upper() == 0): return '0'
    v = math.nextafter(v0, math.inf)
    if abs(v) < 1e-300: return '1e-300'
    e = math.floor(math.log10(abs(v))) - (d - 1)
    y = v*(1 + 1e-12) if v > 0 else v*(1 - 1e-12)
    m = math.ceil(y/10.0**e)
    return _fmt(m, e)
if __name__ == '__main__':
    from flint import ctx
    for s in ('1.14449999', '0.5468', '2.09e-6', '6.76e21', '-0.0004'):
        x = arb(s, 1e-12); print(s, fdn(x), fup(x))
    x = arb(1)/3; print(fdn(x), fup(x), fdn(-x), fup(-x))
