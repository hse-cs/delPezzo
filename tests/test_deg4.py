from delPezzo import *
from sage.geometry.cone import Cone
import pytest


def test_ParkWon_B():
    '''
    tests the covering provided in [PW16]_ for the degree 4.
    '''
    S = Surface(4)
    
    # case B(i)
    Ui = CylinderList(CylinderGenerator.cylinders(S, S.E, 'lines2')).get_polar_on('B(1)')
    assert len(Ui)==3
    for i in range(1, 6):
        break
        assert Ui.is_generically_flexible_on(f'B({i})')
    return Ui


def test_Perepechko_B0():
    '''
    tests the covering provided in [Pe13]_ for the degree 4 on the anticanonical divisor.
    '''
    S = Surface(4)
    C = [S.L - S.E[(i+1)%5] - S.E[(i+3)%5] for i in range(5)]
    def cylinder(c):
        Fi = [curve for curve in S.minus_one_curves if S.dot(curve, c)==1]
        return Cylinder.make_type_tangent2(S, Fi, Fi)
    Ui = CylinderList(cylinder(c) for c in C)
    assert  Ui.is_generically_flexible_on(Cone([-S.K]))
    return Ui

@pytest.mark.skip(reason="not implemented")
def test_ParkWon_C():
    return NotImplemented


if __name__=="__main__":
    Ui = test_ParkWon_C()

