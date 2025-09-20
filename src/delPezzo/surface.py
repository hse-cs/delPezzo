#from sage.all import *    #type: ignore
# uncomment the above line for type checking in VSCode, or comment it for doctesting with `sage -python -m doctest surface.py`
#from delPezzo.picard import *
from delPezzo.picard import Curve, PicMap, PicMarked
from delPezzo.cone import Cone_relint

from sage.matrix.constructor import matrix, Matrix
from sage.matrix.matrix_integer_dense import Matrix_integer_dense
from sage.matrix.special import diagonal_matrix, identity_matrix
from sage.rings.rational_field import QQ
from sage.geometry.toric_lattice import ToricLatticeElement
from sage.combinat.root_system.cartan_matrix import  CartanMatrix
from sage.rings.integer_ring import ZZ
from dataclasses import dataclass, field
import itertools
from functools import cached_property, cache
from collections.abc import Generator, Sequence
from typing import Any, Callable, TypeVar, Self





@dataclass(frozen=True)
class Point:
    '''
    a point on a weak surface S as an intersection of a pair of negative curves.
    We assume that no triple intersections (i.e., Eckardt points) occur and that intersections are transversal.

    INPUT:
        - ``curves`` -- list of curves meeting the point
        - ``validate`` -- whether to check that the point is valid
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

    def negativity(self) -> int:
        '''
        return the minimum of indices of curves meeting the point
        
        TESTS:
            >>> Surface(6,[[1,-1,-1,-1]]).points[0].negativity()
            2
            >>> sum(pt.negativity()==1 for pt in Surface(6,[[0,1,-1,0]]).points)
            2
        '''
        return -min(c.dot(c) for c in self.curves)

    def __repr__(self) -> str:
        return f'Point({self.curves[0]}, {self.curves[1]})'

    def __eq__(self, other) -> bool:
        '''
        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Point.by_names(P, "E_2", "L_{12}") == Point.by_names(P, "L_{12}", "E_2")
            True
            >>> Point.by_names(P, "E_2", "L_{12}") == None
            False
        '''
        if other is None:
            return False
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
        - res_curves -- a list of all negative curves on the surface with self-intersection at most -2
        - points -- a list of intersection points of negative curves under assumption that no triple intersections occur
        - is_delPezzo -- a boolean indicating whether the surface is del Pezzo
        - is_weak_delPezzo -- a boolean indicating whether the surface is a (possibly weak) del Pezzo
    '''
    def __init__(self, degree:int, NE_gens:Sequence[ToricLatticeElement|list[int]]|None=None, extra:dict[str,str]|None=None, Q:Matrix_integer_dense|None=None, K:list[int]|None=None, minus_one_curves_included:bool=False) -> None:
        '''
            Initialize a projective surface that is a blowup of P2. 

            Usually a (weak) del Pezzo surface.
        INPUT:
            - ``degree`` -- An integer between 1 and 9, inclusive, representing the degree of the del Pezzo surface.
            - ``NE_gens`` -- a list of generators of the Mori cone. Usually negative curves, possibly except (-1)-curves.
            - ``extra`` -- Optional additional data. 
            - ``Q`` -- The intersection matrix of the lattice. By default we use the coordinates corresponding to a blowup of P2.
            - ``K`` -- The canonical divisor of the surface. - ``minus_one_curves_included`` -- indicates whether the (-1)-curves are provided or should be computed.

        TESTS:
            >>> Surface(6)
            del Pezzo surface of degree 6
            >>> Surface(9).NE_gens
            [L]
            >>> Surface(8).NE_gens
            [L_1, E_1]
            >>> Surface(7).NE_gens
            [E_1, E_2, L_{12}]
        '''
        self.degree = degree
        if self.degree<1  or self.degree>9 :
            raise ValueError("degree must be between 1 and 9")
        blowups = 9 - degree
        if NE_gens is None:
            NE_gens = []
        if Q == None or K == None:
            Q = diagonal_matrix([1]+[-1]*blowups)
            K = [-3] + [1]*blowups
            if blowups == 0:
                NE_gens = [[1]]
                minus_one_curves_included = True
            if blowups == 1:
                NE_gens = [[1,-1],[0,1]]
                minus_one_curves_included = True                
        else:
            assert Q.rank()==blowups+1, "wrong degree"
        super().__init__(Q, NE_gens, minus_one_curves_included   )
        self.K = self.N(K) # canonical divisor
        self.K.set_immutable()
        
        self.extra = extra if extra != None else dict()        

        self.is_delPezzo = all(c.dot(c)==-1 for c in self.neg_curves)
        self.is_weak_delPezzo = all(c.dot(c)>=-2 for c in self.neg_curves)


    @classmethod
    def Hirzebruch(cls, r:int) -> Self:
        '''
        return Hirzebruch surface F_r

        TESTS:
            >>> Surface.Hirzebruch(2)
            weak del Pezzo surface of degree 8 with singularities ('A1',)
             (-2)-curves: [N(0, 1)]
        '''
        return cls(8, NE_gens=[[1,0],[0,1]], Q=Matrix([[0,1],[1,-r]]), K=[r+2,2], minus_one_curves_included=True)

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
    def res_curves(self) -> list[Curve]: 
        """
        return a list of all negative curves on the surface with self-intersection at most -2.

        They correspond to the resolution of singularities of the anticanonical model.

        TESTS:
            >>> Surface(6).res_curves
            []
            >>> len(Surface(6,[[1,-1,-1,-1]]).res_curves)
            1
        """
        return [c for c in self.neg_curves if c.dot(c) <= -2]


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
            raise ValueError(f"Wrong number of candidate points ({len(candidates)}) on the intersection of {input_curves}")
        return candidates[0]




    # @cached_property    
    # def triple_intersections(self): 
    #     '''
    #     Possible triple intersections
    #     '''
    #     return [Point(frozenset([a,b,c])) for a,b,c in itertools.combinations(self.minus_one_curves, 3 ) if self.dot(a,b)*self.dot(b,c)*self.dot(a,c)>0 ]


    @cached_property
    def Ample(self):
        print("Warning: void usage of Ample in favor of NE") # reason: NE has 240 rays in degree 1, and Ample has around 20k rays.
        return Cone_relint(self.dual_cone(self.NE.cone))

    @cache
    def singularity_type(self) -> tuple[str,...]:
        '''
        return alphabetically ordered tuple of singularities as strings in the format `Rn`, where R is the type A,D, or E, and n is the rank.
        
        This is a coarse identifier of the combinatorial type of a weak del Pezzo surface. Not applicable to other surfaces.

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

        if not self.is_weak_delPezzo:
            raise ValueError("this function is only applicable to (weak) del Pezzo surfaces, got:\n", self)

        if len(self.minus_two_curves)==0:
            return tuple()
        T = CartanMatrix(-self.gram_matrix(self.minus_two_curves))
        T = T.cartan_type()._type
        if T.is_reducible():
            return tuple(sorted([cartan_type_to_string(t) for t in T.component_types()]))
        return (cartan_type_to_string(T),)


    def __str__(self) -> str:
        if self.is_delPezzo:
            name = "del Pezzo surface"
            detail = ""
        elif self.is_weak_delPezzo:
            name = "weak del Pezzo surface"
            detail = f" with singularities {self.singularity_type()}"
        else:
            name = "projective surface"
            detail = f" with {len(self.res_curves)} curves of self-intersection <= -2"
        return f"{name} of degree {self.degree}{detail}"


    def __repr__(self) -> str:
        text = str(self)
        if self.extra:
            text += f",\n extra: {self.extra}"
        if not self.is_delPezzo:
            text += "\n (-2)-curves: " + str(self.res_curves)
        return text

    def _complete_partial_isomorphism_with(self, other: 'Surface', partial: list[tuple[Curve,Curve]], source_candidates: list[Curve], destination_candidates: list[Curve]) -> Generator['Isomorphism', None, None]:
        '''
        return all isomorphisms satisfying the partial data

        INPUT:
            - other -- other surface
            - partial -- list of (source, destination) pairs
            - source_candidates -- list of curves in self to send
            - destination_candidates -- list of curves in other that we can send to

        TESTS:
            >>> S = Surface(6)
            >>> isoms = list(S._complete_partial_isomorphism_with(S, [],S.neg_curves, S.neg_curves)); len(isoms)
            12
            >>> all(phi.check() for phi in isoms)
            True
        '''
        if Matrix([p[0] for p in partial]).rank() == self.rank:
            new_candidate = Isomorphism.from_curve_images(self, other, partial)
            if new_candidate != None:
                yield new_candidate
            return
    
        if len(source_candidates) == 0:
            return
        
        candidate = source_candidates[0]
        def image_is_correct(c):
            return all(self.dot(candidate, pair[0]) == other.dot(c, pair[1]) for pair in partial)
        images = [c for c in destination_candidates if image_is_correct(c)]
        
        for i in images:
            new_partial = partial + [(candidate, i)]
            new_src_candidates = [c for c in source_candidates if c != candidate]
            new_dest_candidates = [c for c in destination_candidates if c != i]
            yield from self._complete_partial_isomorphism_with(other, new_partial, new_src_candidates, new_dest_candidates)

    def is_P1xP1(self)->bool:
        '''
        check if self is the direct product of projective lines
        
        TESTS:
            >>> Surface(6).is_P1xP1()
            False
            >>> Surface(9).is_P1xP1()
            False
        '''
        return all(self.dot(c,c)==0 for c in self.NE_gens)

    def isomorphisms(self, other: 'Surface') -> Generator['Isomorphism', None, None]:
        """
        return all isomorphisms from self to other

        TESTS:
            >>> S = Surface(6); len(list(S.isomorphisms(S)))
            12
            >>> S = Surface(8); len(list(S.isomorphisms(S)))
            1
        """
        if self.rank <= 2:
            yield from self._complete_partial_isomorphism_with(other, [], self.NE_gens, other.NE_gens)
            return
        
        max_subset = self.disjoint_subsets_of_max_size(self.minus_one_curves)[0]
        for other_max_subset in other.disjoint_subsets_of_max_size(other.minus_one_curves):
            for permuted_other_max_subset in itertools.permutations(other_max_subset):
                partial = list(zip(max_subset, permuted_other_max_subset)) + [(self.K, other.K)]
                yield from self._complete_partial_isomorphism_with(other, partial, self.res_curves, other.res_curves)


    def isomorphism(self, other: 'Surface') ->'Isomorphism|None':
        """
        return an isomorphism from self to other if exists

        TESTS:
            >>> S = Surface(6); S.isomorphism(S)
            Isomorphism(
            src=del Pezzo surface of degree 6,
            dest=del Pezzo surface of degree 6,
            map=
            [1 0 0 0]
            [0 1 0 0]
            [0 0 1 0]
            [0 0 0 1])
            >>> Surface(6).isomorphism(Surface(6,[[1,-1,-1,-1]]))
        """
        return next(self.isomorphisms(other), None)


    #TODO this is a hack, since we don't explicitly fix a standard map to P2. Sometimes we do, through parent
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
                curve_images = [self.curve(M*c) for c in self.res_curves]
                if all(c in curve_images for c in self.res_curves):
                    yield Isomorphism(self, self, M)
            except ValueError:
                continue





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

    def __mul__(self, other: 'PicMap[Surface] | Isomorphism | Any') -> 'PicMap[Surface] | Isomorphism | Any':
        if type(other) == Isomorphism:
            return Isomorphism(self.src, other.dest, self.map*other.map)
        elif type(other) == PicMap[Surface]:
            return super().__mul__(other)
        else:
            return other.__rmul__(self) #type: ignore

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
        elif isinstance(elem, Curve) and self.src.dot(elem,elem)<0:
            return self.neg_curves_map[elem]
        else:
            return super().__call__(elem)

    @classmethod
    def from_curve_images(cls, src: Surface, dest: Surface, curve_images: list[tuple[Curve, Curve]]) -> Self|None:
        '''
        return an isomorphism from src to dest that sends curves as in curve_images or None if the resulting isomorphism is not well-defined

        the set of curves must be of full rank

        INPUT:
            - src -- source surface
            - dest -- destination surface
            - curve_images -- list of tuples, where each tuple is a pair of a source curve and its image

        TESTS:
            >>> S = Surface(6)
            >>> src_curves = [S.curve("E_1"), S.curve("E_2"), S.curve("E_3"), S.K]
            >>> dest_curves = [S.curve("L_{12}"), S.curve("L_{23}"), S.curve("L_{13}"), S.K]
            >>> phi = Isomorphism.from_curve_images(S, S, list(zip(src_curves, dest_curves)))
            >>> phi(S.curve("E_1"))
            L_{12}
        '''
        src_as_cols = Matrix([c[0] for c in curve_images]).T
        dest_as_cols = Matrix([c[1] for c in curve_images]).T
        if src_as_cols.rank() != src.rank:
            raise ValueError("the set of curves must be of full rank")
        M = dest_as_cols * src_as_cols.pseudoinverse()
        try:
            M = M.change_ring(ZZ)
        except (TypeError, ValueError):
            return None
        if abs(M.det()) != 1:
            raise ValueError(f"the map matrix is not invertible, {M}")
        try:
            isom = cls(src, dest, M)
        except (ValueError, TypeError): 
            return None
        if isom.check():
            return isom

    def __repr__(self) -> str:
        return f"Isomorphism(\nsrc={self.src},\ndest={self.dest},\nmap=\n{self.map})"