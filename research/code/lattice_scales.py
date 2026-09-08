"""Lattice scale-setting: the two-loop bare-coupling relation between beta and the lattice Lambda.

One implementation, because more than one claim rests on it. The dimensionless ratios the scaling
tests turn on -- Delta/(a*Lambda_lat) in Sec 8.7b and sqrt(sigma)/Lambda_lat in Sec 8.8 -- are
constant only if a*Lambda is right, so a slip here moves both sections in the same direction and
neither would contradict the other.

The test suite deliberately keeps its own separate copy: a test that imported this module could not
catch an error inside it. That duplication is the point, and is exempted by name in
test_no_certificate_is_implemented_twice.
"""
import math


def a_lambda(beta, N=2):
    """a * Lambda_lat from the two-loop lattice beta-function, for SU(N) at bare coupling beta.

    beta = 2N/g^2, and the two-loop integration gives
        a*Lambda = (b0 g^2)^(-b1 / 2 b0^2) * exp(-1 / (2 b0 g^2)),
    with the universal coefficients b0 = 11N/48pi^2 and b1 = 34N^2 / 3(16pi^2)^2.
    """
    b0 = 11 * N / (48 * math.pi ** 2)
    b1 = 34 * N ** 2 / (3 * (16 * math.pi ** 2) ** 2)
    g2 = 2.0 * N / beta
    return (b0 * g2) ** (-b1 / (2 * b0 ** 2)) * math.exp(-1.0 / (2 * b0 * g2))
