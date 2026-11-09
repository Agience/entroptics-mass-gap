"""Dobrushin-Shlosman-type box criterion at the unit: the mean boundary influence on one box.

Box V of side L sites with the outside frozen; Gaussian field, precision A = -Lap + mu^2 (mu = m a). The W1 influence
of a boundary site y on the conditional marginal at x in V is k(x, y) = |d E[phi_x | outside] / d phi_y| (the
conditional variance does not depend on the outside). The DS (C_V)-form sum, per site of the box, is
    rho_V = (1/|V|) sum_{x in V} sum_{y outside} k(x, y) = mean_x h_x,   A_VV h = b,   b_x = #outside neighbours of x,
h_x the probability that the killed walk from x leaves V. Since A_VV 1 = mu^2 1 + b, h = 1 - mu^2 A_VV^{-1} 1, so
rho_V = 1 - mu^2 <1, A_VV^{-1} 1>/|V|, computed exactly in the separable sine basis (Dirichlet, no Fourier transform of
the lattice operator: the sine modes are the eigenvectors of the box). Massless: rho_V = 1 exactly at every L.
Criterion: rho_V <= rho* < 1 at fixed physical box side m L a. Run: python ds_unit.py (prints the table)."""
import numpy as np


def rho(d, L, mL):
    mu2 = (mL / L) ** 2
    k = np.arange(1, L + 1)
    lam = 2 - 2 * np.cos(np.pi * k / (L + 1))
    s = np.sin(np.pi * np.outer(np.arange(1, L + 1), k) / (L + 1)) * np.sqrt(2 / (L + 1))
    c = s.sum(axis=0)  # <1, e_k> in 1D
    grids = np.meshgrid(*([lam] * d), indexing="ij", sparse=True)
    cg = np.meshgrid(*([c ** 2] * d), indexing="ij", sparse=True)
    den = mu2 + sum(grids)
    num = 1.0
    for g in cg:
        num = num * g
    q = float((num / den).sum())
    return 1 - mu2 * q / L ** d


out = []
def p(s):
    print(s, flush=True); out.append(s)
for d, Ls in ((2, (8, 16, 32, 64, 128)), (4, (8, 16, 24, 32, 40))):
    p(f"# d = {d}: rho_V (box side L sites, physical side m*L*a = mL); massless rho = 1")
    p("mL    " + "  ".join(f"L={L:4d}" for L in Ls))
    for mL in (0.0, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0):
        # DERIVED: mL = 0 is the massless row, where rho_V = 1 exactly (A_VV 1 = b, so h = 1)
        p(f"{mL:5.1f} " + "  ".join(f"{rho(d, L, mL):.4f}" if mL > 0 else "1.0000" for L in Ls))
