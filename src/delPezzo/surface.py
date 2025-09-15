#from sage.all import *    #type: ignore
# uncomment the above line for type checking in VSCode, or comment it for doctesting with `sage -python -m doctest surface.py`
#from delPezzo.picard import *
from delPezzo.picard import Curve, PicMap, PicMarked

from sage.matrix.constructor import matrix, Matrix
from sage.matrix.special import diagonal_matrix, identity_matrix
from sage.rings.rational_field import QQ
from sage.geometry.toric_lattice import ToricLatticeElement
from sage.combinat.root_system.cartan_matrix import  CartanMatrix

from dataclasses import dataclass, field
import itertools
from functools import cached_property, cache
from collections.abc import Generator, Sequence
from typing import Any, Callable, Optional, TypeVar





@dataclass(frozen=True)
class Point:
    '''
    a point on a weak surface S as an intersection of a pair of negative curves.
    We assume that no triple intersections (i.e., Eckardt points) occur and that intersections are transversal.

    INPUT:
        - ``curves`` -- list of curves meeting the point
    '''
    curves : tuple[Curve, Curve]
    validate: bool = True

    def __post_init__(self):
        if self.validate:
            assert self.check(), f'point with curves {self.curves} is not valid'

    @classmethod
    def by_names(cls, P: PicMarked, curve1: str, curve2: str, validate:bool=True) -> 'Point':
        '''
        contruct a point on the surface P from names of curves

        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Point.by_names(P, "E_2", "L_{12}")
            Point(E_2, L_{12})
        '''
        return cls((Curve.get_named(P, curve1), Curve.get_named(P, curve2)), validate=validate)

    def check(self) -> bool:
        '''
        check that assumptions hold
        
        TESTS:
            >>> P1 = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Point.by_names(P1,"E_{12}","L_{12}", validate=False).check()
            False
            >>> Point.by_names(P1,"E_2","L_{12}").check()
            True
        '''
        return len(self.curves) == 2 and all(c.dot(c)<0 for c in self.curves) and self.curves[0].dot(self.curves[1]) == 1

    def is_minus_one(self) -> bool:
        '''
        check if the point lies on the intersection of (-1)-curves
        
        TESTS:
            >>> Surface(6,[[1,-1,-1,-1]]).points[0].is_minus_one()
            False
            >>> sum(pt.is_minus_one() for pt in Surface(6,[[0,1,-1,0]]).points)
            2
        '''
        return self.curves[0].dot(self.curves[0]) == -1 and self.curves[1].dot(self.curves[1]) == -1

    def __repr__(self) -> str:
        return f'Point({self.curves[0]}, {self.curves[1]})'

    def __eq__(self, other) -> bool:
        '''
        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Point.by_names(P, "E_2", "L_{12}") == Point.by_names(P, "L_{12}", "E_2")
            True
        '''
        return self.curves == other.curves or self.curves[::-1] == other.curves





T=TypeVar('T')
def eq_class_representatives(permutations:list[Callable[[T],T]], objects:list[T]) -> Generator[T, None, None]:
    '''
    return representatives of equivalence classes of objects under given permutations of those objects

    Note:
        we assume that the permutations comprise a group

    TESTS:
        >>> S = Surface(5)
        >>> permutations = list(S.automorphisms_over_P2())
        >>> list(eq_class_representatives(permutations, S.minus_one_curves))
        [E_1, L_{12}]
        >>> len(list(eq_class_representatives(permutations, S.points)))
        2
    '''
    remaining_objects = objects[:]
    while remaining_objects:
        next_object = remaining_objects.pop(0)
        yield next_object
        orbit = [p(next_object) for p in permutations]
        remaining_objects = [o for o in remaining_objects if o not in orbit]


class Surface(PicMarked): 
    r'''
    This class represents (a combinatorial type of) a possibly weak del Pezzo surface. 

    Attributes:
      Inherited:
        - N --  A ToricLattice object used to represent the Picard lattice of the variety.
        - Q -- A matrix for the dot product in the Picard group.
        - neg_curves -- a list of all negative curves on the surface
        - minus_one_curves -- a list of all (-1)-curves on the surface

      New:
        - degree -- An integer representing the degree of the surface.
        - K -- The canonical divisor of the variety.
        - E -- A list of Curve (or ToricLatticeElement) objects representing the exceptional configurations of the standard blowup from P^2. 
        - L -- A Curve object representing the line class from P^2.
        - NE -- A NE_SubdivisionCone object representing the NE cone.
        - minus_two_curves -- a list of all (-2)-curves on the surface
        - points -- a list of intersection points of negative curves under assumption that no triple intersections occur
        - is_weak -- a boolean indicating whether the surface is weak

    '''
    def __init__(self, degree:int, minus_two_curves:Sequence[ToricLatticeElement|list[int]]|None=None, extra:dict[str,str]|None=None) -> None:
        '''
            Initialize a (weak) del Pezzo surface that is a blowup of P2.

        INPUT:
            - ``degree`` -- An integer between 1 and 9, inclusive, representing the degree of the del Pezzo surface.
            - ``minus_two_curves`` -- a list of (-2)-curves in the coordinates corresponding to a blowup of P2.
            - ``extra`` -- Optional additional data. 

        TESTS:
            >>> Surface(6)
            del Pezzo surface of degree 6
        '''
        self.degree = degree
        if self.degree<1  or self.degree>9 :
            raise ValueError("degree must be between 1 and 9")
        blowups = 9 - degree
        if minus_two_curves is None:
            minus_two_curves = []
        super().__init__(diagonal_matrix([1]+[-1]*blowups), minus_two_curves)
        
        self.extra = extra if extra != None else dict()        
        self.is_weak = len(minus_two_curves)>0

        E = identity_matrix(QQ, blowups+1)[:,1:].columns() 
        self.L = self.N([1] + [0]*blowups)
        # E is the list of exceptional configurations, so the basis is L, E[0], .. , E[n_blowups-1]
        self.E = [self.N(e) for e in E]
        self.K = self.N([-3] + [1]*blowups) # canonical divisor
        for e in self.E:
            e.set_immutable()


        from delPezzo.cone import NE_SubdivisionCone
        self.NE = NE_SubdivisionCone.NE(self)

    @cached_property
    def minus_two_curves(self) -> list[Curve]: 
        """
        return a list of all (-2)-curves on the surface

        TESTS:
            >>> Surface(6).minus_two_curves
            []
            >>> len(Surface(6,[[1,-1,-1,-1]]).minus_two_curves)
            1
        """
        return [c for c in self.neg_curves if c.dot(c) == -2]


    @cached_property    
    def points(self) -> list[Point]: 
        '''
        return a list of points that are double intersections of negative curves, under the assumption that no triple intersections occur

        TESTS:
            >>> len(Surface(6,[[1,-1,-1,-1]]).points)
            3
        '''
        return [Point((a,b)) for a,b in itertools.combinations(self.neg_curves, 2) if self.dot(a,b)>0 ]

    def point(self, input0: Curve|ToricLatticeElement|list[int], input1:Curve|ToricLatticeElement|list[int]) -> Point:
        '''
        return the point on the surface P corresponding to the pair of curves ``input``

        TESTS:
            >>> S = Surface(7, [[0,1,-1]])
            >>> S.point("E_2","E_{12}")
            Point(E_{12}, E_2)
        '''
        input_curves = self.curve(input0), self.curve(input1)
        candidates = [p for p in self.points if all(c in p.curves for c in input_curves)]
        if len(candidates) != 1:
            raise ValueError(f"Wrong number of candidate points ({len(candidates)}) on the intersection of {input}")
        return candidates[0]


    def blowup(self, curves: Sequence[Curve|ToricLatticeElement|list[int]]) -> PicMap['Surface']:
        '''
        return the blowup of this surface at a point lying on provided (-1)-curves (in the quantity of 0, 1 or 2) as a map to a weak del Pezzo surface
        
        TESTS:
            >>> S = Surface(6,[[1,-1,-1,-1]])
            >>> S.blowup([[0,1,0,0]])(S.N([1,2,3,4]))
            N(1, 2, 3, 4, 0)
            >>> S.blowup([]).dest.minus_two_curves
            [L_{123}]
            >>> S.blowup([[0,1,0,0]]).dest.minus_two_curves
            [L_{123}, E_{14}]
        '''
        resulting_minus_two_curves = [
            list(c) + [0] for c in self.minus_two_curves
            ] + [
            list(c) + [-1] for c in curves
        ]
        new_surface = Surface(self.degree-1, resulting_minus_two_curves)
        map_matrix = identity_matrix(QQ, self.rank+1)[:,:-1]
        return PicMap[Surface](self, new_surface, map_matrix)


    def blowups(self) -> Generator['PicMap[Surface]', None, None]:
        '''
        return all blowups of this surface as maps to weak del Pezzo surfaces
        
        TESTS:
            >>> len(list(Surface(6,[[1,-1,-1,-1]]).blowups()))
            4
            >>> len(list(Surface(7,[[0,1,-1]]).blowups()))
            4
            >>> [len(phi.dest.minus_two_curves) for phi in Surface(7,[[0,1,-1]]).blowups()]
            [1, 2, 2, 3]
            >>> S = Surface(9)
            >>> list(S.blowups())[0](Curve.make(S,[1]))
            N(1, 0)
        '''
        if self.degree<=3:
            raise NotImplementedError
        for additional_minus_two_curves in [[]] + [[c] for c in self.minus_one_curves]  + [pt.curves for pt in self.points if pt.is_minus_one()]:
            yield self.blowup(additional_minus_two_curves)





    # @cached_property    
    # def triple_intersections(self): 
    #     '''
    #     Possible triple intersections
    #     '''
    #     return [Point(frozenset([a,b,c])) for a,b,c in itertools.combinations(self.minus_one_curves, 3 ) if self.dot(a,b)*self.dot(b,c)*self.dot(a,c)>0 ]


    @cached_property
    def Ample(self):
        print("Warning: void usage of Ample in favor of NE") # reason: NE has 240 rays in degree 1, and Ample has around 20k rays.
        return self.dual_cone(self.NE.cone)

    def singularity_type(self) -> tuple[str]:
        '''
        return alphabetically ordered tuple of singularities as strings in the format `Rn`, where R is the type A,D, or E, and n is the rank.
        
        This is a coarse identifier of the combinatorial type of the surface.

        TESTS:
            >>> Surface(7).singularity_type()
            ()
            >>> Surface(6,[[1,-1,-1,-1]]).singularity_type()
            ('A1',)
            >>> Surface(5,[[0,1,-1,0,0], [0,0,0,1,-1]]).singularity_type()
            ('A1', 'A1')
            >>> Surface(4,[[0,1,-1,0,0,0],[0,0,1,-1,0,0],[0,0,0,0,1,-1]]).singularity_type()
            ('A1', 'A2')
        '''
        def cartan_type_to_string(T):
            return f"{T.type()}{T.rank()}"

        if len(self.minus_two_curves)==0:
            return tuple()
        T = CartanMatrix(-self.gram_matrix(self.minus_two_curves))
        T = T.cartan_type()._type
        if T.is_reducible():
            return tuple(sorted([cartan_type_to_string(t) for t in T.component_types()]))
        return (cartan_type_to_string(T),)


    def __str__(self) -> str:
        return f"{'weak ' if self.is_weak else ''}del Pezzo surface of degree {self.degree}{f' with singularities {self.singularity_type()}' if self.is_weak else ''}"


    def __repr__(self) -> str:
        text = str(self)
        if self.extra:
            text += f",\n extra: {self.extra}"
        if self.is_weak:
            text += "\n (-2)-curves: " + str(self.minus_two_curves)
        return text

    def isomorphisms(self, other: 'Surface') -> Generator['Isomorphism', None, None]:
        """
        return all isomorphisms from self to other


        """
        raise NotImplementedError
    
    def automorphisms_over_P2(self) -> Generator['Isomorphism', None, None]:
        """
        return all automorphisms of self that are permutations of exceptional configurations E[i]

        TESTS:
            >>> len(list(Surface(5,[[0,1,-1,0,0]]).automorphisms_over_P2()))
            2
            >>> S = Surface(7)
            >>> g = list(S.automorphisms_over_P2())[1]
            >>> g(S.curve("E_2"))
            E_1
        """
        for permutation in itertools.permutations(range(self.rank-1)):
            M = matrix.zero(self.rank)
            M[0,0] = 1
            for i, j in enumerate(permutation):
                M[i+1,j+1] = 1
            try:
                curve_images = [self.curve(M*c) for c in self.minus_two_curves]
                if all(c in curve_images for c in self.minus_two_curves):
                    yield Isomorphism(self, self, M)
            except ValueError:
                continue


    def blowups_nonequivalent_over_P2(self) -> Generator[PicMap['Surface'], Any, None]:
        '''
        return representatives of equivalence classes of blowups of self under automorphisms over P2
        
        TESTS:
            >>> [blowup.dest.minus_two_curves for blowup in Surface(7).blowups_nonequivalent_over_P2()]
            [[], [E_{13}], [L_{123}], [E_{13}, L_{123}]]
        '''

        if self.degree<=3:
            raise NotImplementedError
        yield self.blowup([])
        automorphisms = list(self.automorphisms_over_P2())
        curve_representatives = eq_class_representatives(automorphisms, self.minus_one_curves)
        for c in curve_representatives:
            yield self.blowup([c])
        point_representatives = eq_class_representatives(automorphisms, [pt for pt in self.points if pt.is_minus_one()])
        for pt in point_representatives:
            yield self.blowup(pt.curves)



@dataclass
class Isomorphism(PicMap[Surface]):
    '''
    represents an isomorphism between surfaces
    '''
    neg_curves_map: dict[Curve, Curve] = field(init=False)
    points_map: dict[Point, Point] = field(init=False)

    def __post_init__(self):
        '''
        initialize map on curves and points

        TESTS:
            >>> S = Surface(7)
            >>> phi = Isomorphism(S,S,Matrix([[1,0,0],[0,0,1],[0,1,0]]))
            >>> phi.neg_curves_map[S.curve("E_1")]
            E_2
            >>> phi.points_map[S.point("E_1","L_{12}")]
            Point(E_2, L_{12})
        '''
        self.neg_curves_map = {c: self.dest.curve(super().__call__(c)) for c in self.src.neg_curves}
        self.points_map = {pt: self.dest.point(*tuple(self.neg_curves_map[c] for c in pt.curves)) for pt in self.src.points}

    def check(self) -> bool:
        '''
        check that the map is correct
        '''
        super_check = super().check() and super().is_isomorphism()
        point_check = len(self.src.points) == len(self.dest.points)
        return super_check and point_check

    def __call__(self, elem: ToricLatticeElement | Curve | Point):
        '''
        return image of a divisor class, a negative curve or a point

        TESTS:
            >>> S = Surface(7)
            >>> phi = Isomorphism(S,S,Matrix([[1,0,0],[0,0,1],[0,1,0]]))
            >>> phi(S.curve("E_1"))
            E_2
            >>> phi(S.point("E_1","L_{12}"))
            Point(E_2, L_{12})
        '''
        if isinstance(elem, Point):
            return self.points_map[elem]
        elif isinstance(elem, Curve):
            return self.neg_curves_map[elem]
        elif isinstance(elem, ToricLatticeElement):
            return super()(elem)
        else:
            raise TypeError(f"type of elem must be a ToricLatticeElement, a Curve or a Point; got {type(elem)}")