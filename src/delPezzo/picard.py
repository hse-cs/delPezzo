from dataclasses import dataclass
from typing import Self
#from sage.all_cmdline import *   # import sage library, otherwise other imports break #type: ignore
from sage.matrix.constructor import matrix, Matrix
from sage.matrix.special import diagonal_matrix, identity_matrix
from sage.rings.rational_field import QQ
from sage.geometry.toric_lattice import ToricLatticeElement, ToricLattice, ToricLattice_ambient
from sage.geometry.cone import Cone, ConvexRationalPolyhedralCone, normalize_rays
import itertools
from functools import cached_property, cache
from collections.abc import Generator, Sequence
import textwrap
from sage.rings.integer_ring import ZZ

class PicardLattice:
    r'''
    This class represents a Picard lattice of a smooth rational projective surface.
    
    Attributes:
        N: An ToricLattice object used to represent the Picard lattice of the variety.
        Q: A matrix for the dot product in the Picard lattice.
    '''
    def __init__(self, Q:Matrix) -> None:
        '''
            Initialize a PicardLattice object with the intersection matrix.

        INPUT:
            - ``Q`` -- The intersection matrix of the lattice.

        TESTS:
            >>> Q = diagonal_matrix([1,-1]); PicardLattice(Q)
            PicardLattice(
            [ 1  0]
            [ 0 -1])
        '''
        self.rank : int = Q.rank()
        self.N : ToricLattice_ambient = ToricLattice(self.rank)
        self.Q : Matrix = Q

    def dot(self, a:ToricLatticeElement, b:ToricLatticeElement) -> int:
        '''
        return the self-intersection number of classes a,b

        TESTS:
            >>> L = PicardLattice(diagonal_matrix([1,-1]))
            >>> L.dot(L.N([1,0]),L.N([0,1]))
            0
            >>> L.dot(L.N([1,1]),L.N([1,1]))
            0
            >>> L.dot(L.N([0,1]),L.N([0,1]))
            -1
        '''
        return a*self.Q*b

    def gram_matrix(self, rays: Sequence[ToricLatticeElement]) -> Matrix:
        '''
        return the Gram matrix of the list of classes `rays`

        TESTS:
            >>> L = PicardLattice(diagonal_matrix([1,-1]))
            >>> L.gram_matrix((L.N([0,1]),L.N([1,1])))
            [-1 -1]
            [-1  0]
        '''
        return matrix([[self.dot(a,b) for a in rays] for b in rays])


    def _N_to_M(self, ray:ToricLatticeElement)->ToricLatticeElement:
        '''
        return the class as a linear function on N, i.e., an element of the dual lattice M
        
        TESTS:
            >>> L = PicardLattice(diagonal_matrix([1,-1])) # F_1
            >>> L._N_to_M(L.N([1,-1]))
            M(1, 1)
            >>> L = PicardLattice(Matrix([[0,1],[1,0]])) # P^1 x P^1
            >>> L._N_to_M(L.N([1,0]))
            M(0, 1)
        '''
        M = self.N.dual()
        ray = ray * self.Q
        return M(ray)

    def dual_cone(self, input: ConvexRationalPolyhedralCone | Sequence[ToricLatticeElement]) -> ConvexRationalPolyhedralCone:
        '''
        return the dual cone in the Picard lattice

        INPUT:
            - ``input`` -- A cone or a list of generating rays in the Picard lattice

        TESTS:
            >>> L = PicardLattice(diagonal_matrix([1,-1]))
            >>> L.dual_cone([L.N([1,0]),L.N([1,1])]).rays()
            N(0, -1),
            N(1,  1)
            in 2-d lattice N
        '''
        if isinstance(input, ConvexRationalPolyhedralCone):
            input = input.rays()
        return Cone([self._N_to_M(r) for r in input]).dual()

    def __repr__(self) -> str:
        return f"PicardLattice(\n{self.Q})"

#TODO arithmetic operations on curves should return ToricLatticeElement
class Curve(ToricLatticeElement):
    '''
    The Picard class of an irreducible curve on a surface
    '''

    @classmethod
    def make(cls, P: PicardLattice, vector: list[int]|ToricLatticeElement, standard_basis: bool = True):
        """
        Create a Curve object with given coordinates and an optional name.

        INPUT:
            P: the Picard lattice
            coordinates: The coordinates representing the curve.
            standard_basis: If True, the coordinates are assumed to be in the standard basis of the Picard lattice of the blowup of P2, namely L, E_1,..,E_k.

        TESTS:
            >>> Curve.make(PicardLattice(diagonal_matrix([1,-1])), [1,-1])
            L_1
            >>> Curve.make(PicardLattice(Matrix([[0,1],[1,0]])), [1,0], standard_basis=False)
            N(1, 0)
        """
        if isinstance(vector, ToricLatticeElement):
            vector = list(vector)
        try:
            curve = cls(P.N, vector)
        except:
            raise ValueError(f"invalid coordinates {vector} in {P.N}")
        curve.set_immutable()
        curve.Pic = P
        
        curve.name = Curve.get_name(curve) if standard_basis else str(P.N(vector))
        return curve

    @classmethod
    def get_named(cls,  P: 'PicMarked', name: str):
        '''
        get a negative curve on `P` by its name

        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> Curve.get_named(P, "E_2")
            E_2
        '''
        for curve in P.neg_curves:
            if curve.name == name:
                return curve
        else:
            raise ValueError(f"Curve {name} not found in negative curves")

    def dot(self, other:'Curve') -> int:
        '''
        return the self-intersection number of this curve and the other one

        TESTS:
            >>> C = Curve.make(PicardLattice(diagonal_matrix([1,-1])), [1,-1])
            >>> C.dot(C) 
            0
        '''
        if self.Pic != other.Pic:
            raise ValueError("The curves must be in the same Picard lattice")
        product = self.Pic.dot(other, self)
        return product

    def __repr__(self) -> str:
        if not hasattr(self, 'name'):
            raise AttributeError(f"Curve {super().__repr__()} not initialized")
        return self.name

    #TODO names for P1 x P1 ? forget for now
    @classmethod
    def get_name(cls, curve:ToricLatticeElement)-> str:
        '''
        return the following name of a curve C
            E_i for C=[0,0,..1,..0],
            E_{ij} for C=E_i-E_j
            L_{i_1 i_2 ...} for C=L-E_{i_1}-E_{i_2}...
            Q_{i_1 i_2 ...} for C=2L- sum(E_j) + E_{i_1} + E_{i_2}...
            coordinates of curve otherwise
        '''
        curve = list(curve)
        if curve[0] == 0:
            i,j = None, None
            if 1 in curve:
                i = curve.index(1)
            if -1 in curve:
                j = curve.index(-1)
            if not all(k==i or k==j for k in range(len(curve)) if curve[k]!=0):
                return str(curve)
            if i and j:
                return "E_{" + str(i) + str(j) + "}"
            if i:
                return f"E_{i}"
        if curve[0] == 1:
            minus_one_indices = [c for c in range(len(curve)) if curve[c]==-1]
            if not all(f==0 or f==-1 for f in curve[1:]):
                return str(curve)
            if len(minus_one_indices) == 0:
                return "L"
            if len(minus_one_indices) == 1:
                return "L_" + str(minus_one_indices[0])
            return "L_{" + "".join(str(c) for c in minus_one_indices) + "}"
        if curve[0] == 2:
            if not all(f==0 or f==-1 for f in curve[1:]):
                return str(curve)
            zero_indices = [c for c in range(len(curve)) if curve[c]==0]
            if len(zero_indices) == 0:
                return "Q"
            if len(zero_indices) == 1:
                return "Q_" + str(zero_indices[0])
            return "Q_{" + "".join(str(c) for c in zero_indices) + "}"
        if curve[0] == 3:
            if not all(f==0 or f==-1 for f in curve[1:]):
                return str(curve)
            zero_indices = [c for c in range(len(curve)) if curve[c]==0]
            if len(zero_indices) == 0:
                return "-K"
            return "-K+" + "+".join(f"E_{c}" for c in zero_indices)
        return str(curve)


@cache
def candidate_minus_one_curves(degree) -> list['Curve']:
    '''
    return list of possible (-1)-curve classes in standard coordinates for a smooth rational projective surface of anticanonical degree ``degree``

    TESTS:
        >>> candidate_minus_one_curves(8)
        [N(0, 1)]
        >>> len(candidate_minus_one_curves(3))
        27
    '''
    blowups = 9  - degree
    N = ToricLattice(blowups+1)
    E = identity_matrix(QQ, blowups+1)[:,1:].columns() 
    L = N([1] + [0]*blowups)
    
    exceptional_curves = [e for i,e in enumerate(E)]
    lines = [L-E[i]-E[j] for i,j in itertools.combinations(range(len(E)), 2 )]
    conics = [2 *L-sum(E[i] for i in points) for points in itertools.combinations(range(len(E)), 5 )]
    cubics = [3 *L-sum(points)-double for points in itertools.combinations(E, 7 ) for double in points]
    curves = exceptional_curves + lines + conics + cubics
    if degree <= 1 :
        quartics = [4 *L-sum(E) - sum(double_points) for double_points in itertools.combinations(E, 3 )]
        quintics = [5 *L-sum(E) - sum(double_points) for double_points in itertools.combinations(E, 6 )]
        sextics = [6 *L-2 *sum(E) - triple_point for triple_point in E]
        curves += quartics + quintics + sextics
    return normalize_rays(curves, N)



class PicMarked(PicardLattice):
    r'''
    This class represents a Picard lattice marked with a cone of curves (i.e., the Mori cone).
    
    In most cases rays of the cone are exactly classes of negative irreducible curves.
    
    Attributes:
        N: An ToricLattice object used to represent the Picard lattice of the variety.
        Q: A matrix for the dot product in the Picard lattice.
        NE_gens: list classes of classes generating the Mori cone.
        neg_curves: the set of the classes of the negative curves
    '''
    def __init__(self, Q:Matrix, NE_gens:Sequence[ToricLatticeElement|list[int]]|None=None, minus_one_curves_included:bool=False) -> None:
        '''
            Initialize a PicMarked object with the intersection matrix and classes of negative curves.

        INPUT:
            - ``Q`` -- The intersection matrix of the lattice.
            - ``NE_gens`` -- a list of generators of the Mori cone. Usually they are negative curves in the coordinates corresponding to a blowup of P2.
            - ``minus_one_curves_included`` -- indicates whether the (-1)-curves are provided or should be computed. 

        TESTS:
            >>> PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            PicMarked(
            [ 1  0  0]
            [ 0 -1  0]
            [ 0  0 -1],
            neg_curves: [E_{12}, E_2, L_{12}])
            >>> P=PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]]); P.NE.rays()
            N(0,  1, -1),
            N(0,  0,  1),
            N(1, -1, -1)
            in 3-d lattice N
            >>> P1xP1 = PicMarked(Matrix([[0,1],[1,0]]),[[1,0],[0,1]], minus_one_curves_included=True); P1xP1.NE.rays()
            N(1, 0),
            N(0, 1)
            in 2-d lattice N
        '''
        super().__init__(Q)
        if NE_gens is None:
            NE_gens = []
        NE_gens = [self.N(c) for c in NE_gens]
        if not minus_one_curves_included:
            if not all(self.dot(c,c)<0 for c in NE_gens):
                raise ValueError("You must provide (-1)-curves if there is a non-negative NE generator")
            neg_curves = NE_gens
            minus_one_curves = candidate_minus_one_curves(10-self.rank)
            minus_one_curves =  [c for c in minus_one_curves if all(self.dot(c,f)>=0 for f in neg_curves)]
            NE_gens = list(neg_curves) + minus_one_curves
        standard_basis = Q.is_diagonal() and Q[0,0] == 1 and all(Q[i,i]==-1 for i in range(1,Q.rank()))
        self.NE = Cone(NE_gens, self.N)
        self.NE_gens : list['Curve'] = [Curve.make(self,curve, standard_basis) for curve in self.NE.rays()]
        self.check()

    def check(self) -> bool:
        '''
        check that all provided generators are rays of the Mori cone

        TESTS:
            >>> PicMarked(Matrix([[0,1],[1,0]]),[[1,0],[0,1]], minus_one_curves_included=True).check()
            True
        '''
        return all(c in self.NE.rays() for c in self.NE_gens)


    @cached_property
    def neg_curves(self):
        '''
        return negative curves among generators of the Mori cone

        TESTS:
            >>> P1xP1=PicMarked(Matrix([[0,1],[1,0]]),[[1,0],[0,1]], minus_one_curves_included=True); P.neg_curves
            []
        '''
        return [c for c in self.NE_gens if c.dot(c)<0]

    @cached_property
    def minus_one_curves(self) -> list['Curve']:
        '''
        return a list of all (-1)-curves

        TESTS:
            >>> P=PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]]); P.minus_one_curves
            [E_2, L_{12}]
        '''
        return [c for c in self.neg_curves if c.dot(c)==-1]

    def curve(self, input: str | ToricLatticeElement | list[int]) -> 'Curve':
        '''
        return the curve satisfying the input: either by name or by coordinates
        
        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> P.curve([0,0,1])
            E_2
            >>> P.curve("E_2")
            E_2
        '''
        if isinstance(input, str):
            return Curve.get_named(self, input)        
        elif isinstance(input, ToricLatticeElement):
            input = list(input)
        candidates = [c for c in self.neg_curves if list(c)==list(input)]
        if len(candidates) != 1:
            #raise ValueError(f"did not find a curve {input}")
            return Curve.make(self, input)
        return candidates[0]

    def curves_not_meeting(self, curves_to_filter: Sequence['Curve'], test_curves: Sequence['Curve']) -> list['Curve']:
        '''
        return the list of curves in ``curves_to_filter`` do not meet any of the curves ``test_curves``

        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> P.curves_not_meeting(P.neg_curves, [P.curve("E_{12}")])
            [L_{12}]
        '''
        return [c for c in curves_to_filter if all(self.dot(c,c2)==0  for c2 in test_curves)]

    def disjoint_subsets(self, curves:list['Curve'], maximal_only:bool=False) -> Generator[list['Curve']]:
        '''
        return subsets of curves from ``curves`` that are pairwise disjoint. If ``maximal_only`` is True, return only subsets maximal by inclusion

        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> list(P.disjoint_subsets(P.neg_curves))
            [[E_{12}, L_{12}], [E_{12}], [E_2], [L_{12}], []]
            >>> list(P.disjoint_subsets(P.neg_curves, maximal_only=True))
            [[E_{12}, L_{12}], [E_2]]
        '''
        if len(curves) == 0 :
            yield []
            return
        curve = curves[0]
        orthogonal_curves = [c for c in curves[1:] if self.dot(c,curve)==0]
        # subsets that contain curve:
        for subset in self.disjoint_subsets(orthogonal_curves, maximal_only=maximal_only):
                yield [curve] + subset
        # subsets that do not contain curve
        for subset in self.disjoint_subsets(curves[1:], maximal_only=maximal_only):
            if maximal_only and all(curve.dot(c)==0 for c in subset):
                continue
            yield subset
            
    def disjoint_subsets_of_max_size(self, curves:list['Curve']) -> list[list[Curve]]:
        '''
        return subsets of maximal size
        
        TESTS:
            >>> P = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> P.disjoint_subsets_of_max_size(P.neg_curves)
            [[E_{12}, L_{12}]]
            >>> P = PicMarked(diagonal_matrix([1,-1,-1,-1,-1,-1,-1]))
            >>> len(P.disjoint_subsets_of_max_size(P.neg_curves))
            72
        '''

        maximal_subsets_by_inclusion = list(self.disjoint_subsets(curves, maximal_only=True))
        max_size = max(len(subset) for subset in maximal_subsets_by_inclusion)
        return [subset for subset in maximal_subsets_by_inclusion if len(subset)==max_size]



    def __repr__(self) -> str:
        '''
        represent the marked lattice

        TESTS:
            >>> PicMarked(Matrix([[0,1],[1,0]]),[[1,0],[0,1]], minus_one_curves_included=True)
            PicMarked(
            [0 1]
            [1 0],
            neg_curves: []
            other_NE_gens=[N(1, 0), N(0, 1)])
            >>> PicMarked(Matrix([[1]]),[[1]], minus_one_curves_included=True)
            PicMarked(
            [1],
            neg_curves: []
            other_NE_gens=[L])
        '''
        non_neg_gens = [c for c in self.NE_gens if c not in self.neg_curves]
        non_neg_gens_string = "" if len(non_neg_gens)==0 else f"\nother_NE_gens={non_neg_gens}"
        return f"PicMarked(\n{self.Q},\nneg_curves: {self.neg_curves}{non_neg_gens_string})"
            

@dataclass
class PicMap[T: PicardLattice]:
    '''
    represents a map between Picard lattices, marked Picard lattices, or surfaces
    '''
    src: T
    dest: T
    map: Matrix


    def __repr__(self) -> str:
        '''
        return an identifying string representation of the map

        TESTS:
            >>> P1 = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> P2 = PicardLattice(diagonal_matrix([1,-1]))
            >>> PicMap(P1, P2, Matrix([[1,0,0],[0,1,0]]))        
            PicMap(
                src=PicMarked(
                [ 1  0  0]
                [ 0 -1  0]
                [ 0  0 -1],
                neg_curves: [E_{12}, E_2, L_{12}]),
                dest=PicardLattice(
                [ 1  0]
                [ 0 -1]),
                map=
                [1 0 0]
                [0 1 0])
        '''
        return "PicMap("+textwrap.indent(f"\nsrc={self.src},\ndest={self.dest},\nmap=\n{self.map})", "    ")

    def check(self) -> bool:
        '''
        verify that the map are correctly defined

        TESTS:
            >>> P1 = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> P2 = PicardLattice(diagonal_matrix([1,-1]))
            >>> PicMap(P1, P2, Matrix([[1,0,0],[0,1,0]])).check()
            True
            >>> PicMap(P1, P2, Matrix([[1,0],[0,0]])).check()
            False
        '''
        dimensions_ok = self.map.ncols() == self.src.rank and self.map.nrows() == self.dest.rank

        #TODO check that the product is preserved?

        #if isinstance(self.src, PicMarked) and isinstance(self.dest, PicMarked): #TODO check that curves go to curves? no, the image may be reducible or non-negative
        return dimensions_ok


    def __mul__(self, other: Self| 'PicMap[T]') -> 'PicMap[T]':
        
        '''
        return the composition of two maps

        TESTS:
            >>> BlF1 = PicMarked(diagonal_matrix([1,-1,-1]))
            >>> F1 = PicMarked(diagonal_matrix([1,-1]))
            >>> P1xP1 = PicMarked(matrix([[0,1],[1,0]]))
            >>> phi = PicMap(BlF1,F1,Matrix([[1,0,0],[0,1,0]]))
            >>> psi = PicMap(P1xP1,BlF1,Matrix([[1,1],[1,0],[0,1]]))
            >>> (phi*psi).map
            [1 1]
            [1 0]
        '''
        if other.dest != self.src:
            raise ValueError(f"These maps are not composable:", self, other)
        return PicMap[T](src=other.src, dest=self.dest, map=self.map*other.map)
    
    def __call__(self, D: ToricLatticeElement) -> ToricLatticeElement:
        '''
        apply the map to the divisor class D

        TESTS:
            >>> BlF1 = PicMarked(diagonal_matrix([1,-1,-1]))
            >>> F1 = PicMarked(diagonal_matrix([1,-1]))
            >>> phi = PicMap(BlF1,F1,Matrix([[1,0,0],[0,1,0]]))
            >>> phi(BlF1.neg_curves[0])
            N(0, 1)
        '''
        return self.dest.N(self.map*D)
    
    def is_isomorphism(self) -> bool:
        '''
        return True if the map is an isomorphism of (marked) Picard lattices

        TESTS:
            >>> BlF1 = PicMarked(diagonal_matrix([1,-1,-1]))
            >>> Bl2F1 = PicMarked(diagonal_matrix([1,-1,-1]), [[0,1,-1]])
            >>> F1 = PicardLattice(diagonal_matrix([1,-1]))
            >>> F1_marked = PicMarked(diagonal_matrix([1,-1]))
            >>> PicMap(BlF1,F1,Matrix([[1,0,0],[0,1,0]])).is_isomorphism()
            False
            >>> PicMap(F1,F1_marked,Matrix([[1,0],[0,-1]])).is_isomorphism()
            True
            >>> PicMap(F1_marked,F1_marked,Matrix([[1,0],[0,-1]])).is_isomorphism()
            False
            >>> PicMap(F1,F1,Matrix([[0,1],[1,0]])).is_isomorphism()
            False
            >>> PicMap(Bl2F1, BlF1, diagonal_matrix([1,1,1])).is_isomorphism()
            False
        '''
        if isinstance(self.src, PicMarked) and isinstance(self.dest, PicMarked):
            if {tuple(c) for c in self.dest.NE_gens} != {tuple(self(c)) for c in self.src.NE_gens}:
                return False
        if not (self.map.is_square() and (abs(self.map.det()) == 1)):
            return False
        src_basis = self.src.N.basis()
        if src_basis == None:
            raise ValueError("The toric lattice must have a basis")
        if not self.dest.gram_matrix([self(b) for b in src_basis]) == self.src.Q: 
            return False
        return True
    

