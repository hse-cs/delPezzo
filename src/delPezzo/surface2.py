from typing import Iterable
from delPezzo.surface import Surface
#from sage.all import *

from delPezzo.contraction import Contraction
from delPezzo.surface import *

#TODO blowup of P1xP1 has wrong matrix


#TODO should inherit from Point?


@dataclass(frozen=True)
class Stratum:
    '''
    a stratum on a weak surface S
    
    We consider the stratification of S by negative curves. A stratum is defined by the tuple of negative curves that contain it.
    We assume that no triple intersections (i.e., Eckardt points) occur and that intersections are transversal.

    Fields:
        - ``curves`` -- list of curves meeting the point
        - ``check`` -- whether to check that the stratum is valid
    '''
    curves : tuple[Curve, ...]
    check: bool = True

    def __post_init__(self):
        if self.check:
            assert self._check(), f'stratum with curves {self.curves} is not valid'

    @classmethod
    def by_names(cls, P: PicMarked, curves: Iterable[str], check:bool=True) -> Self:
        '''
        contruct a stratum on the surface P from names of curves

        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Stratum.by_names(P, ["E_2", "L_{12}"])
            Stratum([E_2, L_{12}])
        '''
        return cls(tuple(Curve.get_named(P, c) for c in curves), check=check)

    def _check(self) -> bool:
        '''
        check that assumptions hold
        
        TESTS:
            >>> P1 = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Stratum.by_names(P1,["E_{12}","L_{12}"], check=False)._check()
            False
            >>> Stratum.by_names(P1,["E_2","L_{12}"])._check()
            True
        '''
        if len(self.curves) > 2:
            return False
        if any(c.dot(c)>=0 for c in self.curves):
            return False
        if len(self.curves) == 2 and self.curves[0].dot(self.curves[1]) != 1:
            return False
        return True

    def negativity(self) -> int:
        '''
        return the minimum of indices of curves meeting the point
        
        TESTS:
            >>> Stratum.from_pt(Surface(6,[[1,-1,-1,-1]]).points[0]).negativity()
            2
            >>> sum(Stratum.from_pt(pt).negativity()==1 for pt in Surface(6,[[0,1,-1,0]]).points)
            2
        '''
        return -min(c.dot(c) for c in self.curves)

    def __repr__(self) -> str:
        return f'Stratum({self.curves})'

    def __eq__(self, other) -> bool:
        '''
        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Stratum.by_names(P, ["E_2", "L_{12}"]) == Stratum.by_names(P, ["L_{12}", "E_2"])
            True
        '''
        return set(self.curves) == set(other.curves)

    def dim(self):
        '''
        return dimension of self

        TESTS:
            >>> Stratum.from_pt(Surface(6,[[1,-1,-1,-1]]).points[0]).dim()
            2
        '''
        return 2-len(self.curves)

class Surface2(Surface):
    '''
    surface endowed with blowups and contractions
    '''    

    @classmethod
    def convert_surface(cls, S:Surface) -> Self:
        '''
        convert Surface object into Surface2 (a hack)
        '''
        S.__class__ = cls
        return S 

    def negativity(self):
        """
        return minimal self-intersection of negative curves as an absolute value
        
        TESTS:
            >>> Surface2(6,[[1,-1,-1,-1]]).negativity()
            2
        """
        return -min([c.dot(c) for c in self.neg_curves], default=0)


    def blowup(self, curves: Sequence[Curve|ToricLatticeElement|list[int]]) -> Contraction:
        '''
        return the blowup of this surface at a point lying on provided negative curves (in the quantity of 0, 1 or 2) as a contraction to self from the new surface

        ARGUMENTS:
            - ``curves`` -- a list of negative curves that contain the blown up point
        
        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> S.blowup([[0,1,0,0]]).pullback_map(S.N([1,2,3,4]))
            N(1, 2, 3, 4, 0)
            >>> S.blowup([]).src.minus_two_curves
            [L_{123}]
            >>> S.blowup([[0,1,0,0]]).src.minus_two_curves
            [L_{123}, E_{14}]
        '''
        resulting_neg_curves = [
            list(c) + [0] for c in self.neg_curves if c not in curves and c.dot(c)<=-2
            ] + [
            list(c) + [-1] for c in curves
        ]
        new_surface = Surface(self.degree-1, resulting_neg_curves) #TODO only if Q is standard, but CombTypes works
        map_matrix = identity_matrix(QQ, self.rank+1)[:,:-1]
        e = new_surface.curve([0]*self.rank+[1])
        blowup = PicMap[Surface](self, new_surface, map_matrix)
        contraction = Contraction(new_surface, self, map_matrix.T, [e],[e], blowup)
        return contraction


    def strata(self, blowup_negativity:int=2) -> list[list[Curve]]: #TODO output Stratum
        '''
        return possible loci for a point on `self` w.r.t. negative curves as a list of negative curves passing through it

        ARGUMENTS:
            - ``blowup_negativity`` -- the minimal allowed self-intersection of negative curves after the blowup (under assumption that negative curves are smooth)
        
        TESTS:
            >>> Surface2(7).strata()
            [[], [E_1], [E_2], [L_{12}], [E_1, L_{12}], [E_2, L_{12}]]
            >>> Surface2(7,[[0,1,-1]]).strata(1)
            [[], [E_{12}, E_2], [E_2, L_{12}]]
        '''
        return [[]] + [[c] for c in self.neg_curves if c.dot(c)>-blowup_negativity] + [list(pt.curves) for pt in self.points if pt.negativity()<blowup_negativity]


    def blowups(self, blowup_negativity:int=2) -> Generator[Contraction, None, None]:
        '''
        return all blowups of this surface as maps to generated surfaces
        
        ARGUMENTS:
            - ``negativity`` -- the minimal allowed self-intersection of negative curves

        TESTS:
            >>> len(list(Surface2(6,[[1,-1,-1,-1]]).blowups()))
            4
            >>> len(list(Surface2(7,[[0,1,-1]]).blowups()))
            4
            >>> [len(phi.dest.minus_two_curves) for phi in Surface2(7,[[0,1,-1]]).blowups()]
            [1, 2, 2, 3]
            >>> S = Surface2(9)
            >>> list(S.blowups())[0](Curve.make(S,[1]))
            N(1, 0)
        '''
        if self.degree<=3:
            raise NotImplementedError
        for stratum in self.strata(blowup_negativity):
            yield self.blowup(stratum)



    def blowups_nonequivalent_over_P2(self, blowup_negativity:int=2) -> Generator[Contraction, Any, None]:
        '''
        return representatives of equivalence classes of blowups of self under automorphisms over P2
        
        we assume all negative curves to be smooth

        ARGUMENTS:
            - ``negativity`` -- a boundary on the self-intersection number of strict transforms of negative curves

        TESTS:
            >>> [contraction.src.minus_two_curves for contraction in Surface2(7).blowups_nonequivalent_over_P2()]
            [[], [E_{13}], [L_{123}], [E_{13}, L_{123}]]
        '''

        if self.degree<=3:
            raise NotImplementedError
        yield self.blowup([])
        automorphisms = list(self.automorphisms_over_P2())
        curve_representatives = eq_class_representatives(automorphisms, [c for c in self.neg_curves if c.dot(c)>-blowup_negativity])
        point_representatives = eq_class_representatives(automorphisms, [p for p in self.points if p.negativity() < blowup_negativity])
        for c in curve_representatives:
            yield self.blowup([c])
        for pt in point_representatives:
            yield self.blowup(pt.curves)
