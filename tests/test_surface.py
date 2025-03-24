from sage.all_cmdline import *   # import sage library, otherwise other imports break #type: ignore
from sage.geometry.toric_lattice import ToricLattice

from collections import Counter
import pytest

from delPezzo import Surface, Curve

def test_disjoint_subsets():
    S = Surface(5)
    C = Counter(len(s) for s in S.disjoint_subsets(S.minus_one_curves)).most_common()
    assert C == [(3, 30), (2, 30), (1, 10), (4, 5), (0, 1)]



@pytest.mark.parametrize("N, coords, expected", [
    (ToricLattice(3), [0,0,1], "E_2"),
    (ToricLattice(4), [0,1,0,0], "E_1"),
    (ToricLattice(4), [0,0,-1,1], "E_{32}"),
    (ToricLattice(3), [1,0,-1], "L_2"),
    (ToricLattice(3), [1,0,0], "L"),
    (ToricLattice(4), [2,-1,-1,-1], "Q"),
    (ToricLattice(4), [3,-1,-1,-1], "-K"),
    (ToricLattice(4), [3,-1,0,-1], "-K+E_2"),
    (ToricLattice(7), [2,0,0,0,-1,-1,-1], "Q_{123}"),
    (ToricLattice(7), [2,-1,0,-1,-1,-1,-1], "Q_2"),
])
def test_curve_name(N, coords, expected):
    assert Curve.name(N(coords)) == expected

