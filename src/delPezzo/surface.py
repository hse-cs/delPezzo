#from sage.all_cmdline import *   # import sage library, otherwise other imports break #type: ignore
from sage.matrix.constructor import matrix, Matrix
from sage.matrix.special import diagonal_matrix, identity_matrix
from sage.rings.rational_field import QQ
from sage.geometry.toric_lattice import ToricLatticeElement
from sage.combinat.root_system.cartan_matrix import  CartanMatrix
from sage.quadratic_forms.quadratic_form import QuadraticForm

from dataclasses import dataclass, field
import itertools
from functools import cached_property, cache
from collections.abc import Generator, Sequence
from typing import Optional

from .picard import *

class Surface(PicMarked): 
    r'''
    This class represents a generic (possibly weak) del Pezzo surface. It implements the curve classes in the Picard lattice and allows working with cylinders on the surface.

    Attributes:
        degree: An integer representing the degree of the surface.
        N: An ToricLattice object used to represent the Picard lattice of the variety.
        K: The canonical divisor of the variety.
        E: A list of Curve (or ToricLatticeElement) objects representing the exceptional curves of the standard blowup from P^2. TODO make this a list of (maybe reducible) orthogonal (-1)-curves
        L: A Curve object representing the line class from P^2.
        Q: A matrix for the dot product in the Picard group.
        NE: A NE_SubdivisionCone object representing the NE cone.
        minus_one_curves: a list of all (-1)-curves on the surface
        minus_two_curves: a list of all (-2)-curves on the surface

    EXAMPLES::
        >>> S = Surface(5)
        >>> cylinders = [c for c in S.all_cylinders(['P1xP1', 'lines', 'tangent'])]
        >>> cone = NE_SubdivisionCone.representative(S,'B(0)'); cone
        1-d cone in 5-d lattice N
        >>> collection = CylinderList(cylinders)
        >>> covering = collection.get_polar_on(cone).reduce()
    '''
    def __init__(self, degree:int, minus_two_curves:Sequence[ToricLatticeElement], extra:dict[str,str]|None=None) -> None:
        '''
            Initialize a Surface object with the given degree and optional extra data.S

        INPUT:
            - ``degree`` -- An integer between 1 and 9, inclusive, representing the degree of the del Pezzo surface.
            - ``minus_two_curves`` -- a list of (-2)-curves in the coordinates corresponding to a blowup of P2.
            - ``extra`` -- Optional additional data. 
        '''
        if self.degree<1  or self.degree>9 :
            raise ValueError("degree must be between 1 and 9")
        super.__init__(1+9-degree, neg_curves)
        
        self.extra = extra if extra != None else dict()

        self.dependencies = dependencies or WeakDependencies()
        assert self.dependencies.is_valid()
        self.is_weak = not self.dependencies.is_trivial()
        assert degree <= self.dependencies.degree_estimate()
        blowups = 9  - degree
        self.degree = degree

        E = identity_matrix(QQ, blowups-1)[:,1:].columns() 
        self.L = self.N([1] + [0]*blowups)
        # E is the set of exceptional curves, so the basis is L, E[0], .. , E[n_blowups-1]
        self.E = [self.N(e) for e in E]
        self.K = self.N([-3] + [1]*blowups) # canonical divisor
        for e in self.E:
            e.set_immutable()


        from .cone import NE_SubdivisionCone
        self.NE = NE_SubdivisionCone.NE(self)

    def singularity_type(self):
        if len(self.minus_two_curves)==0:
            return 'A0'
        T = CartanMatrix(-self.gram_matrix(self.minus_two_curves))
        return T.cartan_type()

    #TODO test that blowups give exactly Lubbes' list except P1xP1
    def blowups(self):
        if self.degree<=3:
            raise NotImplementedError
        p = 9-self.degree
        
        deps = self.dependencies
        #lines = [line for line in lines if all(cls._point_line_and_chain_align(line, chain) for chain in self.infinitesimal_chains)]
        
        #listing all possibilities for infinitesimal_chains after adding a new point
        new_chains_variants = [deps.infinitesimal_chains]
        for i in range(len(deps.infinitesimal_chains)):
            new_chain = deps.infinitesimal_chains[i] + [p]
            if all(deps._point_line_and_chain_meet_correctly(line, new_chain) for line in deps.collinear_triples):
                new_chains_variants.append(deps.infinitesimal_chains[:i] + [new_chain] + deps.infinitesimal_chains[i+1:])
        union_of_chains = [i for chain in deps.infinitesimal_chains for i in chain]
        for i in range(9-self.degree):
            if i in union_of_chains:
                continue
            new_chain = [[i,p]]
            if all(deps._point_line_and_chain_meet_correctly(line, new_chain) for line in deps.collinear_triples):
                new_chains_variants.append(deps.infinitesimal_chains+new_chain)


        possible_new_conics = [list(five) +[p] for five in itertools.combinations(range(9-self.degree),5)]
        possible_new_conics = [six for six in possible_new_conics if all(len(set(six).intersection(set(six2))) < 5 for six2 in deps.sixs_on_conic)]

        # pairs of points which are not contained in an existing line
        candidate_pairs = [[i,j] for i,j in itertools.combinations(range(9-self.degree),2)  
                        if all(i not in line or j not in line for line in deps.collinear_triples)]
        for chains in new_chains_variants:
            # pairs i,j such that a new line (i,j,p) is ok with chains
            pairs = [pair for pair in candidate_pairs if all(deps._point_line_and_chain_meet_correctly(pair+[p], chain) for chain in chains)]
            # choose disjoint subsets of pairs so that lines do not coincide
            pair_sets = itertools.chain.from_iterable(itertools.combinations(pairs,r) for r in range(len(pairs)+1))
            for pair_set in pair_sets:
                if all(set(a).isdisjoint(b) for a,b in itertools.combinations(pair_set,2)): # if pair_set is disjoint
                    chosen_lines = [pair+[p] for pair in pair_set]
                    new_collinear_triples = deps.collinear_triples+chosen_lines
                    conics_candidates = [six for six in possible_new_conics if all(not set(triple).issubset(set(six)) for triple in new_collinear_triples)]
                    conic_subsets = itertools.chain.from_iterable(itertools.combinations(conics_candidates, r) for r in range(len(conics_candidates)+1))
                    for conic_subset in conic_subsets:
                        if all(len(set(six1).intersection(set(six2))) < 5 for six1, six2 in itertools.combinations(conic_subset, 2)):
                            new_deps = WeakDependencies(collinear_triples=new_collinear_triples, infinitesimal_chains=chains, sixs_on_conic=deps.sixs_on_conic+list(conic_subset))
                            yield Surface(self.degree-1, dependencies=new_deps)
            

    #def contract_minus_one_curves(self, curve:ToricLatticeElement) -> :

    #def is_blowdown(self, curves:list[ToricLatticeElement]) -> bool:

    # def contractions(self, contracted_curves:list[ToricLatticeElement]|None=None, curves_not_to_contract:list[ToricLatticeElement]|None=None, maximal_only=False):
    #     if contracted_curves == None:
    #         contracted_curves = []
    #     if curves_not_to_contract == None:
    #         curves_not_to_contract = []
    #     assert self.is_valid_contraction(contracted_curves)
    #     if self.is_maximal_contraction(contracted_curves):
    #         yield contracted_curves
    #     minus_one_curves_after_contraction = [c for c in self.minus_one_curves + self.minus_two_curves if 
    #                                           c not in contracted_curves and 
    #                                           c not in curves_not_to_contract and 
    #                                           self.dot(c,c, contracted_curves=contracted_curves)==-1]
    #     subsets = self.disjoint_subsets(minus_one_curves_after_contraction,independent_with=contracted_curves, maximal_only=False)
    #     for subset in subsets:
    #         if len(subset)==0:
    #             yield contracted_curves
    #             continue
    #         yield from self.contractions(
    #             contracted_curves=contracted_curves+subset,
    #             curves_not_to_contract=curves_not_to_contract + [c for c in minus_one_curves_after_contraction if c not in subset],
    #             maximal_only=maximal_only
    #         )

    def standard_contraction(self) -> 'Contraction':
        standard_contraction_lines = [e for e in self.minus_one_curves + self.minus_two_curves if self.dot(e, self.L) == 0]
        return Contraction(self, standard_contraction_lines)


    def contractions_P2(self) -> Generator['Contraction', None, None]:
        for minus_one_curves_to_contract in self.disjoint_subsets(self.minus_one_curves):
            for minus_two_curves_to_contract in itertools.combinations(self.minus_two_curves, 9-self.degree-len(minus_one_curves_to_contract)):
                contraction = Contraction.make_valid_contraction(self, minus_one_curves_to_contract+list(minus_two_curves_to_contract))
                if contraction != None:
                    #assert contraction.is_maximal()
                    yield contraction
            


        

    def Line(self,exceptional_curves:Sequence[ToricLatticeElement])-> ToricLatticeElement:
        triple_L = -self.K + sum(exceptional_curves)
        assert all(i%3==0 for i in triple_L), f"triple line from K={self.K} and E={exceptional_curves} not divisible by 3"
        return self.N([i/3  for i in triple_L])
        # we can divide by 3 if we provide all exceptional curves for contracting to P2



    @cached_property    
    def double_intersections(self): 
        '''
        Double intersections, which may coincide in triple ones (then 3 double intersections = 1 triple one)
        '''
        return [Point(frozenset([a,b])) for a,b in itertools.combinations(self.negative_curves, 2) if self.dot(a,b)>0 ]

    @cached_property    
    def triple_intersections(self): 
        '''
        Possible triple intersections
        '''
        return [Point(frozenset([a,b,c])) for a,b,c in itertools.combinations(self.minus_one_curves, 3 ) if self.dot(a,b)*self.dot(b,c)*self.dot(a,c)>0 ]

    @cached_property
    def points(self) -> list['Point']:
        return self.double_intersections + [Point(frozenset([c])) for c in self.negative_curves] + [Point(frozenset())]

    #TODO refactor module to avoid usage of Ample in favor of NE through dualities. Reason is, NE has 240 rays in degree 1, and Ample has around 20k rays.
    @cached_property
    def Ample(self):
        return self.dual_cone(self.NE.cone)


    # def cone_representative(self, cone_type:str) -> 'NE_SubdivisionCone':
    #     return NE_SubdivisionCone.representative(self, cone_type)

    def __str__(self) -> str:
        return f"{'weak' if self.is_weak else ''} del Pezzo surface of degree {self.degree}{f' with singularities {self.singularity_type()}' if self.is_weak else ''}"

    def __repr__(self) -> str:
        text = str(self)
        if self.extra:
            text += f",\n extra: {self.extra}"
        if self.is_weak:
            text += "\n" + str(self.dependencies)
        return text

    

class Contraction():    
    '''
    S: A surface that is contracted
    contracted_curves: A tuple of contracted (irreducible) curves on S.
    E: a list of exceptional reducible (-1)-curves, which form an orthogonal basis of the span of the contracted curves. They are sums of chains of contracted (-2)-curves ending with a (-1)-curve.
    C: a list of contracted (irreducible) curves in the same order as E.
    '''
    S:Surface
    contracted_curves: tuple[ToricLatticeElement,...]
    E: tuple[ToricLatticeElement,...]
    C: tuple[ToricLatticeElement,...]

    def __init__(self, S:Surface, contracted_curves: Sequence[ToricLatticeElement]) -> None:
        """
        Initializes a new instance of the class.

        Args:
            S (Surface): The surface object.
            contracted_curves (Sequence[ToricLatticeElement]): A sequence of contracted curves.

        Returns:
            None
        """
        self.S = S
        self.contracted_curves = tuple(contracted_curves)
        E=[]
        C=[]
        assert self.is_valid(), f'contraction of curves {contracted_curves} is not valid'
        for chain in self.chains_of_contracted_curves:
            for i in range(len(chain)):
                C.append(chain[i])
                E.append(sum(chain[i:]))
        assert len(E) == len(C)
        self.E = tuple(E)
        self.C = tuple(C)

    @cached_property
    def chains_of_contracted_curves(self) -> list[list[ToricLatticeElement]]:
        '''
        returns list of lists of curves of form [C1,C2..,Cn], where Ei are irreducible contracted curves such that Cn^2=-1, Ci^2=-2 for i<n, and Ci*C_{i+1}=1.
        '''
        minus_one_curves = [c for c in self.contracted_curves if self.S.dot(c,c)==-1]
        minus_two_curves = [c for c in self.contracted_curves if self.S.dot(c,c)==-2]
        def find_chain(minus_one_curve:ToricLatticeElement)->list[ToricLatticeElement]:
            chain = [minus_one_curve]
            while True:
                next_curves = [c for c in minus_two_curves if self.S.dot(c,chain[-1])==1 and c not in chain]
                match len(next_curves):
                    case 0:
                        return list(reversed(chain))
                    case 1:
                        chain.append(next_curves[0])
                    case _:
                        raise ValueError("more than one next curve, should be a chain")
        return [find_chain(c) for c in minus_one_curves]
                
    def _E_to_C(self, e:ToricLatticeElement)->ToricLatticeElement:
        return self.C[self.E.index(e)]

    def _C_to_E(self, c:ToricLatticeElement)->ToricLatticeElement:
        assert c in self.C, f"{c} is not in {self.C}"
        assert len(self.E) == len(self.C), f"{self.E} and {self.C} have different lengths"
        return self.E[self.C.index(c)]

    @cached_property
    def L(self):
        '''
        returns the class of line on the contracted surface (we assume it to be P2)
        '''
        assert self.is_P2()
        return self.S.Line(self.E)


    def project(self, v):
        return v + sum(self.S.dot(e,v)*e for e in self.E)
        #return self.S.N(self.picard_projection_matrix*v)

    @classmethod
    def is_valid_contraction(cls, S:Surface, curves_to_contract: Sequence[ToricLatticeElement]) -> bool:
        g = S.gram_matrix(curves_to_contract)
        q = QuadraticForm(QQ, g)
        return q.is_negative_definite() and abs(g.det())==1

    @classmethod
    def make_valid_contraction(cls, S:Surface, curves_to_contract: Sequence[ToricLatticeElement]) -> Optional['Contraction']:
        if cls.is_valid_contraction(S, curves_to_contract):
            return cls(S, curves_to_contract)
        return None

    def is_valid(self) -> bool:
        return self.is_valid_contraction(self.S, self.contracted_curves)

    def is_maximal(self) -> bool:
        return all(self.dot(c,c)>=0 for c in 
                   self.S.minus_one_curves+self.S.minus_two_curves)        

    def is_P2(self) -> bool:
        return self.is_maximal() and len(self.contracted_curves) == 9-self.S.degree

    def dot(self, a, b):
        return self.S.dot(self.project(a),self.project(b))

    def gram_matrix(self, rays):
        return matrix([[self.dot(a,b) for a in rays] for b in rays])

    def __repr__(self) -> str:
        return f"contraction of curves {self.contracted_curves} on {self.S}"

    def are_collinear(self, c1, c2, c3) -> bool:
        E = [self._C_to_E(c) for c in (c1,c2,c3)]
        return self.L-sum(E) in self.S.minus_two_curves

    @cached_property
    def conic_classes(self) -> list[tuple[ToricLatticeElement,int]]:
        '''
        return a list of Picard classes of proper transforms of conics in P2, each with the dimension of the corresponding linear system.
        '''
        result = []
        for p in itertools.product(*[range(len(chain)+1) for chain in self.chains_of_contracted_curves]):
            dimension = 5 - sum(p)
            if dimension < 0:
                continue
            curves_on_conic = [curve for i,n in enumerate(p) for
                               curve in self.chains_of_contracted_curves[i][:n]]
            if any(self.are_collinear(c1,c2,c3) for c1,c2,c3 in itertools.combinations(curves_on_conic,3)):
                continue
            conic_class = 2*self.L - sum(self._C_to_E(c) for c in curves_on_conic)
            conic_class.set_immutable()
            result.append([conic_class, dimension])
        return result
    
    @cached_property
    def line_classes(self) -> list[tuple[ToricLatticeElement,int]]:
        '''
        return a list of Picard classes of proper transforms of lines in P2, each with the dimension of the corresponding linear system.
        UPD: actually, they are linear systems, i.e., smaller objects than classes
        '''
        #TODO rewrite by taking all collinear triples, then non-collinear pairs, then single base curves, and then a generic class
        result = []
        for p in itertools.product(*[range(len(chain)+1) for chain in self.chains_of_contracted_curves]):
            dimension = 2 - sum(p)
            if sum(p)>3:
                continue
            curves_on_line = [c for i,n in enumerate(p) for c in self.chains_of_contracted_curves[i][:n]]
            if any(self.are_collinear(c1,c2,c3)==False for c1,c2,c3 in itertools.combinations(curves_on_line,3)):
                continue
            dimension = 2 - len(curves_on_line)
            if dimension == -1:
                if self.are_collinear(*curves_on_line):
                    dimension = 0
                else:
                    continue
            
            # check that if two ci are on line, then another ci collinear with them is on line
            other_curves_meeting_line = [c for c in self.C if any(self.are_collinear(c1, c2, c) for c1, c2 in itertools.combinations(curves_on_line, 2))]            
            if not set(other_curves_meeting_line).issubset(set(curves_on_line)):
                continue
            
            line_class = self.L - sum(self._C_to_E(c) for c in curves_on_line)
            line_class.set_immutable()
            result.append([line_class, dimension])
        return result



    #def check_restraints_on_line(self, curves:Sequence[ToricLatticeElement]) -> bool:


@dataclass(frozen=True)
class Point:
    '''
    a point on a weak surface S as an element of the bubble space of P^2

    INPUT:
        - ``curves`` -- list of curves meeting the point
    '''
    curves : frozenset[Curve]
    # TODO define a proper equality


@dataclass
class BubbleClass:
    '''
    This class represents a bubble class (i.e., a pair of a bubble cycle and a divisor class) on a surface `S` in the category of blowups of P^2, see [Pe23]_ for details. 

    INPUT:
        - ``S`` -- a weak del Pezzo surface
        - ``points`` -- points in the bubble cycle; each point has built-in dependencies with the blowup cycle of S
        - ``inner_dependencies`` -- list of vectors representing the dependencies between points of the bubble cycle
        - ``Picard_class`` -- ToricLatticeElement representing the element of Pic(S) of the bubble class
    '''
    S: 'Surface'
    points: list['Point']
    inner_dependencies: list[ToricLatticeElement] | None
    Picard_class: ToricLatticeElement



