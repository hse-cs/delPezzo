from sage.all_cmdline import *   # import sage library, otherwise other imports break #type: ignore
from sage.matrix.constructor import matrix
from sage.matrix.special import diagonal_matrix, identity_matrix
from sage.rings.rational_field import QQ
from sage.geometry.toric_lattice import ToricLatticeElement, ToricLattice, ToricLatticeFactory
from sage.geometry.cone import Cone, ConvexRationalPolyhedralCone, normalize_rays
from sage.combinat.root_system.cartan_matrix import  CartanMatrix
from sage.quadratic_forms.quadratic_form import QuadraticForm

from dataclasses import dataclass, field
import itertools
from functools import cached_property
from collections.abc import Generator, Sequence
from typing import Optional
from types import MethodType


# def _get_immutable_element(self: ToricLatticeFactory, *args, **kwds):
#     '''
#     contruct a new immutable element of ``self`` 
#     '''
#     element = super().__call__(self, *args, **kwds)
#     element.set_immutable()
#     return element

@dataclass
class WeakDependencies:
    '''
    This class represents dependencies of blowup points for a weak del Pezzo surface obtained from P^2, see [Pe23]_ for details. The numeration of points starts from 0.            

    INPUT: 
            - ``collinear_triples`` -- indices of triples of collinear blown up points.
            - ``infinitesimal_chains`` -- indices of chains of infinitely near blown up points. The next point in the chain is blown up infinitely near to the previous one. 
            - ``sixs_on_conic`` -- six-tuples of indices for six points on a conic if present.
            - ``cusp_cubics`` -- list of indices i for each cuspidal cubic 3*L-E_0-...-E_7-E_i in degree 1 
    
    '''
    collinear_triples: list[list[int]] = field(default_factory=list)
    infinitesimal_chains: list[list[int]] = field(default_factory=list)
    sixs_on_conic: list[list[int]] = field(default_factory=list)
    cusp_cubics: list[int] = field(default_factory=list)

    def is_trivial(self):
        '''
        return False if surface is not weak
        '''
        return len(self.collinear_triples)+len(self.infinitesimal_chains)+len(self.sixs_on_conic)+len(self.cusp_cubics)==0
    
    def degree_estimate(self):
        '''
        return maximal possible degree of the corresponding weak surface based on indices of mentioned points 
        '''
        list_to_flatten = self.collinear_triples + self.infinitesimal_chains + self.sixs_on_conic
        N_points = max([max(chain, default=-1) for chain in list_to_flatten], default=-1)+1 # 0 points for empty lists
        if len(self.cusp_cubics) > 0:
            N_points = max(N_points, 8)
        return 9 - N_points


    def is_valid(self):
        if self.degree_estimate() < 1:
            return False
        triples, chains, conics = self.collinear_triples, self.infinitesimal_chains, self.sixs_on_conic
        degree = self.degree_estimate()

        if degree <1:
            return False

        for triple in triples:
            if  len(triple) != 3 or len(set(triple)) != 3:
                return False

        # two lines intersect only by one point
        for triple1, triple2 in itertools.combinations(triples, 2):
            if len(set(triple1).intersection(set(triple2)))>1:
                return False

        # chains do not have duplicate entries
        if len(set(i for chain in chains for i in chain)) != sum(len(chain) for chain in chains):
            return False
        
        # line can contain only a prefix sublist of a chain
        for triple in triples:
            for chain in chains:
                if not self._point_line_and_chain_meet_correctly(triple, chain):
                    return False
        
        for six in conics:
            for triple in triples:
                if all(p in six for p in triple):
                    return False

        for six1, six2 in itertools.combinations(conics, 2):
            if len([p in six1 for p in six2]) >= 5:
                return False
        
        if degree<=2:
            raise NotImplementedError
        
        return True

    @classmethod
    def _point_line_and_chain_meet_correctly(cls, triple, chain):
        intersection = [i for i in chain if i in triple]
        return all(intersection[i] == chain[i] for i in range(len(intersection)))


    def __repr__(self):
        text = ""
        if self.collinear_triples:
            text += f",\n collinear_triples: {self.collinear_triples}"
        if self.infinitesimal_chains:
            text += f", infinitesimal_chains: {self.infinitesimal_chains}"
        if self.cusp_cubics:
            text += f", cusp_cubics: {self.cusp_cubics}"
        return text


# class BubbleCycle:
#     '''
#     This class represents a bubble cycle on P^2 (or any surface in its category of blowups), see [Pe23]_ for details. 
#     '''

class Surface: 
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
        sage: S = Surface(5)
        sage: cylinders = [c for c in S.all_cylinders(['P1xP1', 'lines', 'tangent'])]
        sage: cone = NE_SubdivisionCone.representative(S,'B(0)'); cone
        1-d cone in 5-d lattice N
        sage: collection = CylinderList(cylinders)
        sage: covering = collection.get_polar_on(cone).reduce()
    '''
    def __init__(self, degree:int, dependencies: WeakDependencies|None=None, extra:dict[str,str]|None=None) -> None:
        '''
            Initialize a Surface object with the given degree and optional extra data.S

        INPUT:
            - ``degree`` -- An integer between 1 and 9, inclusive, representing the degree of the del Pezzo surface.
            - ``dependencies`` -- the dependencies (i.e., (-2)-curves) of blowup points representing this surface as the blowup of P2.
            - ``extra`` -- Optional data to be used in the initialization of non-generic surfaces. The following keys are supported:
            - ``tacnodal_curves`` -- An even integer between 0 and 24, inclusive, representing the number of tacnodal curves. Can be used for the surfaces of degree 2, defaults to zero.
        '''
        if degree<1  or degree>9 :
            raise ValueError("degree must be between 1 and 9")
        
        self._curve_names = dict()
        self.extra = extra if extra != None else dict()

        if degree == 2 :
            if 'tacnodal_curves' in self.extra.keys():
                self.tacnodal_curves = int(self.extra['tacnodal_curves'])
            else:
                self.tacnodal_curves = 0 

        self.dependencies = dependencies or WeakDependencies()
        assert self.dependencies.is_valid()
        self.is_weak = not self.dependencies.is_trivial()
        assert degree <= self.dependencies.degree_estimate()
        blowups = 9  - degree
        self.degree = degree

        self.N = ToricLattice(blowups + 1 )
        #self.N.__call__ = MethodType(_get_immutable_element, self.N)
        E = identity_matrix(QQ, blowups+1 )[:,1:].columns() 
        # E is the set of exceptional curves, so the basis is L, E[0], .. , E[n_blowups-1]
        self.E = [self.N(e) for e in E]
        self.L = self.N([1] + [0]*blowups)
        self.K = self.N([-3] + [1]*blowups) # canonical divisor
        for e in self.E:
            e.set_immutable()
        self.Q = diagonal_matrix([1] + blowups*[-1])

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
            

    def dot(self, a:ToricLatticeElement, b:ToricLatticeElement) -> int:
        return a*self.Q*b

    def gram_matrix(self, rays):
        return matrix([[self.dot(a,b) for a in rays] for b in rays])


    def _N_to_M(self, ray:ToricLatticeElement)->ToricLatticeElement:
        M = self.N.dual()
        return M([r if i==0 else -r for i,r in enumerate(ray)])

    def dual_cone(self, input: ConvexRationalPolyhedralCone | list[ToricLatticeElement]) -> ConvexRationalPolyhedralCone:
        if isinstance(input, ConvexRationalPolyhedralCone):
            input = input.rays()
        return Cone([self._N_to_M(r) for r in input]).dual()


        

    def Line(self,exceptional_curves:Sequence[ToricLatticeElement])-> ToricLatticeElement:
        triple_L = -self.K + sum(exceptional_curves)
        assert all(i%3==0 for i in triple_L), f"triple line from K={self.K} and E={exceptional_curves} not divisible by 3"
        return self.N([i/3  for i in triple_L])
        # we can divide by 3 if we provide all exceptional curves for contracting to P2

    def _add_curve_name(self, curve:'Curve', name:str)->'Curve':
        curve.set_immutable()
        self._curve_names[curve] = name
        return curve

    #TODO move to class Curve?
    # def _curve_name(self, curve:'Curve') -> str:
    #     #print('naming curve ', curve)
    #     if curve in self._curve_names.keys() and curve in self.minus_one_curves+self.minus_two_curves:
    #         return self._curve_names[curve]
    #     else:
    #         return str(curve)

    # def _curves_name(self, curves:Sequence['Curve']) -> str:
    #     return ', '.join([self._curve_name(c) for c in curves])#print('naming curve ', curve)

    @cached_property
    def minus_two_curves(self) -> list['Curve']:
        collinear = [self._add_curve_name(self.L - self.E[i] - self.E[j] - self.E[k], f'L_{i+1}{j+1}{k+1}') for i,j,k in self.dependencies.collinear_triples]
        
        infinitesimal = [self._add_curve_name(self.E[chain[i]]-self.E[chain[i+1]], f'E_{chain[i]}{chain[i+1]}') for chain in self.dependencies.infinitesimal_chains for i in range(len(chain)-1)]
        
        conic = [self._add_curve_name(2*self.L - sum(self.E[i] for i in six), f'Q{"".join(i+1 for i in range(len(self.E)) if i not in six)}') for six in self.dependencies.sixs_on_conic]
        cubic = [3*self.L - sum(self.E) - self.E[i] for i in self.dependencies.cusp_cubics]
        curves = collinear + infinitesimal + conic + cubic
        curves = normalize_rays(curves, self.N)
        return curves

    # def curve_name(self, c) -> str|None:
    #     if c in self.minus_one_curves:
    #         match self.dot(c, self.L):
    #             case 0:
    #                 pass



    @cached_property
    def minus_one_curves(self) -> list['Curve']:
        exceptional_curves = [self._add_curve_name(e, f'E_{i+1}') for i,e in enumerate(self.E)]
        lines = [self._add_curve_name(self.L-self.E[i]-self.E[j], f'L_{i+1}{j+1}') for i,j in itertools.combinations(range(len(self.E)), 2 )]
        conics = [self._add_curve_name(2 *self.L-sum(self.E[i] for i in points), f'Q_{"".join(str(i+1) for i in range(len(self.E)) if i not in points)}') for points in itertools.combinations(range(len(self.E)), 5 )]
        cubics = [3 *self.L-sum(points)-double for points in itertools.combinations(self.E, 7 ) for double in points]
        curves = exceptional_curves + lines + conics + cubics
        if self.degree == 1 :
            quartics = [4 *self.L-sum(self.E) - sum(double_points) for double_points in itertools.combinations(self.E, 3 )]
            quintics = [5 *self.L-sum(self.E) - sum(double_points) for double_points in itertools.combinations(self.E, 6 )]
            sextics = [6 *self.L-2 *sum(self.E) - triple_point for triple_point in self.E]
            curves += quartics + quintics + sextics
        #for c in curves:
         #   c.set_immutable()
        curves = normalize_rays(curves, self.N)
        if self.is_weak:
            curves = [c for c in curves if all(self.dot(c,f)>=0 for f in self.minus_two_curves)]
        return curves
        
    def curves_not_meeting(self, curves_to_filter, test_curves):
        return [c for c in curves_to_filter if all(self.dot(c,c2)==0  for c2 in test_curves)]

    @cached_property    
    def double_intersections(self): 
        '''
        Double intersections, which may coincide in triple ones (then 3 double intersections = 1 triple one)
        '''
        return [Point(frozenset([a,b])) for a,b in itertools.combinations(self.minus_one_curves, 2) if self.dot(a,b)>0 ]

    @cached_property    
    def triple_intersections(self): 
        '''
        Possible triple intersections
        '''
        return [Point(frozenset([a,b,c])) for a,b,c in itertools.combinations(self.minus_one_curves, 3 ) if self.dot(a,b)*self.dot(b,c)*self.dot(a,c)>0 ]

    #TODO refactor module to avoid usage of Ample in favor of NE through dualities. Reason is, NE has 240 rays in degree 1, and Ample has around 20k rays.
    @cached_property
    def Ample(self):
        return self.dual_cone(self.NE.cone)

    def disjoint_subsets(self, curves:list[Curve], maximal_only:bool=False) -> Generator[Curve]:
        '''
        return subsets of curves that are pairwise disjoint and disjoint with ones in independent_with

        EXAMPLES::
            sage: from collections import Counter
            sage: S = Surface(5)
            sage: Counter(len(s) for s in S.disjoint_subsets(S.minus_one_curves)).most_common()
            [(3, 10), (4, 5)]
        '''
        if maximal_only:
            raise NotImplementedError
        if len(curves) == 0 :
            yield []
            return
        curve = curves[0]
        orthogonal_curves = [c for c in curves[1:] if self.dot(c,curve)==0]
        # subsets that contain curve:
        for subset in self.disjoint_subsets(orthogonal_curves, maximal_only=maximal_only):
                yield [curve] + subset
        # subsets that do not contain curve
        yield from self.disjoint_subsets(curves[1:], maximal_only=maximal_only)
          

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




class Curve(ToricLatticeElement):
    #TODO should be a bubble class with a single curve in its linear system
    def __init__(self, coordinates, name:str|None=None):
        """
        Initialize a Curve object with given coordinates and an optional name.

        INPUT:
            coordinates: The coordinates representing the curve.
            name (str, optional): The name of the curve. Defaults to None.
        """
        super().__init__(coordinates)
        self.name = name
        self.set_immutable()
    #components = []

    def __mul__(self, other:'Curve') -> int:
        product = self.S._N_to_M(other) * self
        return product

    


@dataclass(frozen=True)
class Point:
    curves : frozenset[Curve]
    # TODO define a proper equality

