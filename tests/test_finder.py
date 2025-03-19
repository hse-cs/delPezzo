from delPezzo import Finder, Surface


def test_5():
    S = Surface(5)
    F = Finder(S=S, constructions=['lines', 'lines2', 'tangent'])
    assert F.iterate()
    assert len(F.coverings) == 1
    assert len(F.coverings[0].collection) == 3

def test_6():
    S = Surface(6)
    F = Finder(S=S, constructions=['lines', 'lines2', 'tangent'])
    assert F.all_coverings_are_genflex()
    assert len(F.coverings) == 1
    assert len(F.coverings[0].collection) == 2
    F.iterate()
    assert F.all_coverings_are_genflex()
    assert len(F.coverings) == 1
    assert len(F.coverings[0].collection) == 2
