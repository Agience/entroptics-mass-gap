"""Emit the Lean instance of WeightedProduct.ProfileData at n with an integer sine profile, and the exact
threshold (a2 - K + e) n^4 / a1^2 as a fraction (checked against tree_exact_threshold)."""
import sys, numpy as np
from fractions import Fraction as Fr
# CHOSEN: R = 1000, the integer resolution of the sampled profile; the Lean instance checks every bound exactly
# for the integers emitted, so R sets the profile, not the validity of the check
n = int(sys.argv[1]); p = float(sys.argv[2]); R = 1000
F = [int(round(R*np.sin(np.pi*(x+1)/(2*n))**p)) for x in range(2*n-1)]
f = [F[2*t] for t in range(n)]; g = [F[2*t+1] for t in range(n-1)]
# DERIVED: 0 outside the index range, the profile vanishing off the box
ge = lambda a, t: a[t] if 0 <= t < len(a) else 0
fw = lambda u, v, D: sum(ge(u,t)*ge(v,t+D) for t in range(n))
bw = lambda u, v, r: sum(ge(u,t+r)*ge(v,t) for t in range(n))
def U(u, v, nz=False):
    return max([fw(u,v,D) for D in range(1 if nz else 0, n)] + [bw(u,v,r) for r in range(1, n)])
Uff, Ugg, Ugf, Ufg, Unzff, Unzgg = U(f,f), U(g,g), U(g,f), U(f,g), U(f,f,True), U(g,g,True)
fc = lambda u, v, D: fw(u, v, D)
K = max(Ugf*Ufg*Uff**2, Unzgg*Uff**3, Ugg*Unzff*Uff**2)
a1 = sum(g)*sum(f)**3; a2 = fc(g,g,0)*fc(f,f,0)**3
C = lambda x: fc(f,f,0)**2
e = (2*(K - fc(g,g,1)*fc(f,f,0)**3) + 6*(K - fc(g,g,0)*fc(f,f,1)*fc(f,f,0)**2)
     + 3*((K - fc(g,f,0)*fc(f,g,0)*fc(f,f,0)**2) + (K - fc(g,f,1)*fc(f,g,0)*fc(f,f,0)**2)
          + (K - fc(g,f,0)*fc(g,f,1)*fc(f,f,0)**2) + (K - fc(g,f,1)*fc(g,f,1)*fc(f,f,0)**2)))
t = Fr((a2 - K + e)*n**4, a1**2)
print("# threshold", float(t), t, file=sys.stderr)
print("# U", Uff, Ugg, Ugf, Ufg, Unzff, Unzgg, "K", K, file=sys.stderr)
import json
json.dump(dict(n=n, p=p, f=f, g=g, Uff=Uff, Ugg=Ugg, Ugf=Ugf, Ufg=Ufg, Unzff=Unzff, Unzgg=Unzgg,
               K=K, a1=a1, a2=a2, e=e, t_num=t.numerator, t_den=t.denominator, t=float(t),
               fM=max(f), gM=max(g)), sys.stdout)
