#from sage.all import *

import itertools
from sage.geometry.toric_lattice import ToricLatticeElement
from sage.quadratic_forms.quadratic_form import QuadraticForm
from sage.geometry.cone import Cone, ConvexRationalPolyhedralCone, normalize_rays
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.matrix.constructor import matrix, Matrix
from sage.matrix.special import identity_matrix
from sage.geometry.toric_lattice import ToricLatticeElement, ToricLattice


from dataclasses import dataclass
from functools import cache, cached_property
from typing import Generator, Self, Sequence
from delPezzo.picard import Curve, PicMap
from delPezzo.surface import Isomorphism, Surface

@dataclass
class Contraction(PicMap[Surface]):
    '''
    E: a list of exceptional configurations, i.e., reducible (-1)-curves, which form an orthogonal basis of the span of the contracted curves. 
    C: a list of contracted (irreducible) curves in the same order as E.
    '''
    C: list[Curve]
    E: list[ToricLatticeElement]
    pullback_map: PicMap[Surface]

    @classmethod
    def is_valid_contraction(cls, S:Surface, curves_to_contract: Sequence[Curve]) -> bool:
        '''
        check if provided curves define a smooth contraction

        TESTS:
            >>> S = Surface(5); Contraction.is_valid_contraction(S, [S.curve('E_1')])
            True
            >>> S = Surface(7, [[0,1,-1]]); Contraction.is_valid_contraction(S,[S.curve('E_{12}')])
            False
        '''
        g = S.gram_matrix(curves_to_contract)
        q = QuadraticForm(QQ, g)
        return q.is_negative_definite() and abs(g.det())==1


    @classmethod
    def generate_CE(cls, S:Surface, curves_to_contract: Sequence[Curve]) -> tuple[list[Curve],list[ToricLatticeElement]]:
        '''
        return the list of contracted curves and correspondingly ordered list of pairwise orthogonal (-1)-classes

        TESTS:
            >>> S = Surface(7, [[0,1,-1]]); Contraction.generate_CE(S, [S.curve('E_{12}'), S.curve('E_2')])
            ([E_2, E_{12}], [N(0, 0, 1), N(0, 1, 0)])
        '''
        CE_input = {c:c for c in curves_to_contract}
        CE_output = []
        while CE_input:
            C = next(c for c in CE_input.keys() if S.dot(CE_input[c],CE_input[c])==-1)
            E = S.N(CE_input[C])
            CE_output.append((C,E))
            CE_input.pop(C)
            for c in CE_input.keys():
                CE_input[c] = CE_input[c] + E*S.dot(CE_input[c],E)
        
        return [c for c,_ in CE_output], [S.N(list(e)) for _,e in CE_output]


    @classmethod
    def of_curves(cls, S:Surface, curves_to_contract: Sequence[Curve]) -> Self:
        """
        Returns a contraction of provided curves

        INPUT:
            - S -- The surface object.
            - contracted_curves -- A sequence of negative curves on S.

        TESTS:
            >>> S = Surface(5); Contraction.of_curves(S, [S.curve('E_1')])
            contraction of curves [E_1] on del Pezzo surface of degree 5
            >>> S = Surface(8); e = S.curve('E_1'); Contraction.of_curves(S, [e]).dest.NE_gens
            [L]
            >>> S = Surface(7); e = S.curve('E_1'); Contraction.of_curves(S, [e]).dest.NE_gens
            [E_1, L_1]
        """
        assert cls.is_valid_contraction(S, curves_to_contract=curves_to_contract), 'not a contraction'
        
        C, E = cls.generate_CE(S, curves_to_contract)
        E_perp_as_cone = Cone([S._N_to_M(ray) for e in E for ray in [e,-e]]).dual()
        E_perp = E_perp_as_cone.span()
        A = Matrix(E_perp.basis()).T
        M = (A.T*S.Q*A).inverse()*A.T*S.Q # projection matrix
        #print("A,M:",A,M)
        try:
            M.change_ring(ZZ)
        except TypeError as e:
            print(e, M)
        Q = A.T*S.Q*A
        #NE_images = [M*c for c in S.NE_gens]
        dest_NE = S.NE.intersection(E_perp_as_cone)
        dest_NE_gens = [M*r for r in dest_NE.rays()]
        dest = Surface(S.degree + len(curves_to_contract), dest_NE_gens, Q=Q, K=list(M*S.K), minus_one_curves_included=True)
        pullback_map = PicMap[Surface](src=dest, dest=S, map=A)
        contraction = cls(src=S, dest=dest, map=M, E=E, C=C, pullback_map=pullback_map)
        return contraction

    def _E_to_C(self, e:ToricLatticeElement)->Curve:
        return self.C[self.E.index(e)]

    def _C_to_E(self, c:Curve)->ToricLatticeElement:
        assert c in self.C, f"{c} is not in {self.C}"
        assert len(self.E) == len(self.C), f"{self.E} and {self.C} have different lengths"
        return self.E[self.C.index(c)]


    def __call__(self, D: ToricLatticeElement|Curve) -> ToricLatticeElement|Curve:
        '''
        apply the map to the class or curve D

        TESTS:
            >>> S = Surface(6); sigma = Contraction.of_curves(S, [S.curve("E_1")]); sigma(S.curve("E_2"))
            E_1
            >>> S = Surface(6); sigma = Contraction.of_curves(S, [S.curve("L_{12}")]); c = sigma(S.curve("E_3")); c, isinstance(c, Curve)
            (N(0, 0, 1), True)
        '''
        image = super().__call__(D)
        image_curve = self.dest.curve(list(image))
        if image_curve in self.dest.neg_curves:
            return image_curve
        else:
            return image
        


    def strict_transform(self, curve_in_image:Curve)->Curve:
        '''
        return a strict transform of a negative curve

        TESTS:
            >>> S = Surface(6); sigma = Contraction.of_curves(S, [S.curve("L_{12}")])
            >>> c = sigma(S.curve("E_3")); sigma.strict_transform(c)
            E_3
        '''
        candidates = [c for c in self.src.neg_curves if self(c)==curve_in_image]
        if len(candidates) != 1:
            raise ValueError(f"did not find a negative curve that is a strict transform of {curve_in_image}")
        return candidates[0]
        

    def is_P2(self) -> bool:
        '''
        check if the contraction is onto P^2

        TESTS:
            >>> S = Surface(5); Contraction.of_curves(S, [S.curve('E_1')]).is_P2()
            False
            >>> S = Surface(8); Contraction.of_curves(S, [S.curve('E_1')]).is_P2()
            True
        '''
        return len(self.C) == 9-self.src.degree

    def __mul__(self, other: 'Contraction|Isomorphism | PicMap[Surface]') -> 'Contraction'|PicMap[Surface]:
        '''
        return a composition map of other map and self

        TESTS:
            >>> S1 = Surface(6); sigma1 = Contraction.of_curves(S1, [S1.curve("E_1")])
            >>> S2 = sigma1.dest; sigma2 = Contraction.of_curves(S2,[sigma1(S1.curve("E_2"))])
            >>> sigma2*sigma1
            contraction of curves [E_2, E_1] on del Pezzo surface of degree 6
            >>> phi = Isomorphism(S2,S2,Matrix([[1,0,0],[0,0,1],[0,1,0]]))
            >>> sigma2*phi
            contraction of curves [N(0, 0, 1)] on del Pezzo surface of degree 7
        '''


        if not isinstance(other, (Isomorphism, Contraction)):
            return super().__mul__(other)

        other_pullback_map = other.pullback_map if isinstance(other, Contraction) else PicMap[Surface](src=other.dest, dest=other.src, map=other.map.inverse())

        E = [other_pullback_map(e) for e in self.E]

        if isinstance(other, Contraction):
            E += other.E
            C = [other.strict_transform(c) for c in self.C] + list(other.C)
        else:
            C = [other_pullback_map(c) for c in self.C]

        return self.__class__(other.src, self.dest, self.map*other.map, C, E, other_pullback_map*self.pullback_map)

    #TODO check if ContractionToPlane * Contraction = ContractionToPlane

    def __rmul__(self, other:Isomorphism) -> Self|PicMap[Surface]:
        '''
        return a composition map of an isomorphism and a contraction

        TESTS:
            >>> S1 = Surface(6); sigma1 = Contraction.of_curves(S1, [S1.curve("E_1")])
            >>> S2 = sigma1.dest; sigma2 = Contraction.of_curves(S2,[sigma1(S1.curve("E_2"))])
            >>> phi = Isomorphism(S2,S2,Matrix([[1,0,0],[0,0,1],[0,1,0]]))
            >>> phi*sigma1
            contraction of curves [E_1] on del Pezzo surface of degree 6
        '''
        other_pullback_map = PicMap[Surface](src=other.dest, dest=other.src, map=other.map.inverse())
        return self.__class__(self.src, other.dest, other.map*self.map, self.C, self.E, self.pullback_map*other_pullback_map)

    def __repr__(self) -> str:
        return f"contraction of curves {self.C} on {self.src}"
    
@cache
def candidate_zero_curves(degree:int) -> Sequence[ToricLatticeElement]:
    '''
    return a list of Picard classes in standard blowup coordinates that may arise as pencils of rational 0-curves with an irreducible general fiber
    
    We bound the degree of the image w.r.t. the standard blowup, i.e., we restrict the first coordinate
    
    TESTS:
        >>> candidate_zero_curves(8)
        [N(1, -1)]
        >>> len(candidate_zero_curves(3))
        27
    '''
    blowups = 9  - degree
    N = ToricLattice(blowups+1)
    E = identity_matrix(QQ, blowups+1)[:,1:].columns() 
    L = N([1] + [0]*blowups)
    deg1 =  [L - e for e in E] 
    deg2 = [2*L - sum(e) for e in itertools.combinations(E, 4)] 
    deg3 = [3*L-sum(points)-double for points in itertools.combinations(E, 6) for double in points]
    classes = deg1 + deg2 + deg3
    return normalize_rays(classes, N)

@dataclass
class ContractionToPlane(Contraction):

    @classmethod
    def of_curves(cls, S:Surface, curves_to_contract: Sequence[Curve]) -> Self:
        '''
        return a contraction to P2 of the provided curves on S
        
        TESTS:
            >>> S = Surface(7); ContractionToPlane.of_curves(S, [S.curve("E_1"),S.curve("E_2")])
            ContractionToPlane(src=del Pezzo surface of degree 7, dest=del Pezzo surface of degree 9, map=[1 0 0], C=[E_1, E_2], E=[N(0, 1, 0), N(0, 0, 1)], pullback_map=PicMap(
                src=del Pezzo surface of degree 9,
                dest=del Pezzo surface of degree 7,
                map=
                [1]
                [0]
                [0]))
            >>> S = Surface(6); ContractionToPlane.of_curves(S, [S.curve("E_1"),S.curve("E_2")])
            Traceback (most recent call last):
                ...
            ValueError: not a contraction to P2
        '''
        C = super().of_curves(S, curves_to_contract)
        if not C.is_P2():
            raise ValueError('not a contraction to P2')
        return C



    @cached_property
    def L(self) -> ToricLatticeElement:
        '''
        returns the class of line on the contracted surface (we assume it to be P2)

        TESTS:
            >>> S = Surface(7); ContractionToPlane.of_curves(S, [S.curve("E_1"),S.curve("E_2")]).L
            N(1, 0, 0)
            >>> S = Surface(6); ContractionToPlane.of_curves(S, [S.curve("L_{12}"),S.curve("L_{23}"),S.curve("L_{13}")]).L
            N(2, -1, -1, -1)
        '''
        return self.pullback_map(self.dest.NE.rays()[0])

    def zero_classes(self) -> Sequence[ToricLatticeElement]:
        '''
        return classes of rational zero curves on `src`

        TESTS:
            >>> S = Surface(7); C=ContractionToPlane.of_curves(S, [S.curve("E_1"),S.curve("E_2")]); C.zero_classes()
            [N(1, -1, 0), N(1, 0, -1)]
        '''
        S = self.src

        # suitable candidates in standard coordinates
        curves = [c for c in candidate_zero_curves(S.degree) if all(S.dot(e,c)>=0 for e in S.neg_curves)]
        basis = [self.L] + list(self.E)
        return [sum(i*v for i,v in zip(c, basis)) for c in curves]
