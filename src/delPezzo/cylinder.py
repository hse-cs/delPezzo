from typing import Iterable, Sequence, Generator
from dataclasses import dataclass
import itertools
from functools import cached_property
from collections import Counter

from sage.geometry.cone import ConvexRationalPolyhedralCone, Cone
from sage.geometry.toric_lattice import ToricLatticeElement

from .surface import Surface, Contraction, Curve, Point
from .cone import NE_SubdivisionCone, relint_contains_relint

@dataclass(frozen=True)
class Cylinder:
    '''
    fiber is the generic fiber class of the cylinder (or cylinders if several). If the collection is transversal, then the fiber is empty.
    complement is the list of (-1)-curves lying in the complement of the cylinders' union
    support is the list of (-1)-curves lying in the support of divisors, where the cylinders' union is polar
    '''
    S : Surface
    construction: str|None
    contraction: Contraction|None
    pencil_generators: tuple[Curve, Curve]|None
    complement : tuple[Curve, ...]
    support : tuple[Curve, ...]
    fiber: Curve|None = None
    basepoint: Point|None = None
    transversal: bool|None = None
    dimension: int|None = None

    @classmethod
    def make(cls, S:Surface, complement:list[Curve], support:list[Curve], fiber:Curve|None=None, basepoint:Point|None=None, construction:str|None=None, contraction:Contraction|None=None, pencil_generators:tuple[Curve, Curve]|None=None, transversal:bool|None=None, dimension:int|None=None) -> 'Cylinder':
        for c in complement:
            c.set_immutable()
        for c in support:
            c.set_immutable()
        if fiber!=None:
            fiber.set_immutable()    
        return cls(S, construction, contraction, pencil_generators, tuple(complement), tuple(support), fiber, basepoint, transversal, dimension)

    @classmethod
    def make_type_lines(cls, S:Surface, E:list[Curve], e:Curve)->'Cylinder':
        '''
        We draw lines through image of e and image of one of E, for each of E.
        '''
        L = S.Line(E)
        complement = list(E) + [L-e-f for f in E if f!=e]
        return cls.make(S, complement, complement, L-e, construction='lines', transversal=False)

    @classmethod
    def make_type_lines2(cls, S:Surface, E:list[Curve], e1:Curve, e2:Curve, e3:Curve, e4:Curve)->'Cylinder':
        '''
        See Perepechko-2013, Section 3.1.
        e1, e2, e3, e4 are distinct members of E.
        We draw lines L1 through images of e1 and e2 in P2, L2 through images of e3 and e4. Their images provide a pencil of lines, which gives a cylinder. Other members of E may be assumed to be in different singular fibers.
        '''
        others = [e for e in E if e!=e1 and e!=e2 and e!=e3 and e!=e4]
        assert len(others) == len(E)-4 
        L = S.Line(E)
        lines = [L-e1-e2, L-e3-e4]
        for l in lines:
            l.set_immutable()
        complement = list(E) + [L-e1-e2, L-e3-e4] + [L-e for e in others]
        return cls.make(S, complement, complement, L, basepoint=Point(frozenset(lines)), construction='lines2', transversal = False)

    @classmethod
    def make_type_tangent(cls, S:Surface, E:list[Curve], E_on_conic:Sequence[Curve], E_on_tangent:Sequence[Curve], E_on_fibers: Sequence[Sequence[Curve]]|None = None)->'Cylinder':
        '''
        We draw a conic and a tangent on P2, and specify the positions of blown up points.

        
        Special case:
        See Cheltsov-Park-Won Ex.4.1.2 and Perepechko Ex.5.2. 
        We draw a conic through all blown up points but one, and a tangent line through the remaining one. 
        Technically, for each e we obtain a collection of two cylinders for two tangents respectively. 
        This pair has no common fibers.
        '''
        if E_on_fibers == None:
            E_on_fibers = []
        disjoint_subsets_of_E = [set(E_on_conic), set(E_on_tangent)] + [set(E_on_fiber) for E_on_fiber in E_on_fibers]
        assert len(E) == sum(len(e) for e in disjoint_subsets_of_E) 
        assert len(E) == len(set.union(*disjoint_subsets_of_E))
        L = S.Line(E)
        tangent = L - sum(e for e in E_on_tangent)
        conic = 2*L - sum(e for e in E_on_conic)
        support = list(E) + [conic, tangent] + [2*L - sum(E_on_fiber) for E_on_fiber in E_on_fibers]

        # checks if there are at least two tangents through a given point. 
        two_tangents_through_point = len(E_on_tangent)<=1 and all(len(E_on_fiber)<=1 for E_on_fiber in E_on_fibers)<=1

        #fibers containing at least two Ei
        special_fibers = [E_on_fiber for E_on_fiber in E_on_fibers if len(E_on_fiber)>1]

        # there are at least two tangents such that there is a fiber containing two given points, see CPW Th.6.2.3
        two_tangents_with_fiber_through_two_points = len(E_on_tangent)==0 and len(special_fibers)<=1 and all(len(E_on_fiber)<=2 for E_on_fiber in special_fibers)

        if two_tangents_through_point or two_tangents_with_fiber_through_two_points:            
            complement = list(E) + [conic]
            transversal = True
        else:
            complement = support
            transversal = None
        return cls.make(S, complement, support, 2*L, construction='tangent', transversal=transversal)
    
    @classmethod
    def make_type_tangent_weak(cls, S:Surface, contraction:Contraction, E_on_conic:Sequence[Curve], E_on_tangent:Sequence[Curve], E_on_fibers: list[Sequence[Curve]]|None = None)->'Cylinder':
        '''
        We draw a conic and a tangent on P2, and specify the positions of blown up points.

        Parameters:
            S: the surface
            contraction: the chosen contraction to P2, i.e. a list of contracted curves.
            E_on_Q: the minus-curves on conic Q
            E_on_T: the minus-curves on tangent T. May intersect with E_on_conic.
            E_on_fibers: for each fiber containing at least two minus-curves (except for the intersection of Q and T), there is a list of minus-curves on that fiber. Fibers containing one minus-curve can be omitted. The minus-curves on the intersection of Q and T are omitted.
        
        Remark:
            Instead of (-2)-curves we operate with the corresponding reducible (-1)-curve, i..e., the total transform of a (-1)-curve. So, if E2 is inf. near of E1, and conic preimage contains E2, then it contains E1.
        '''
        if E_on_fibers == None:
            E_on_fibers = []
        
        # TODO just provide classes of L, Q, T, Fi?
        #TODO assertions: lines are in T and not in Q
        assert all(e in contraction.E for e in itertools.chain(E_on_conic,E_on_tangent,*E_on_fibers))

        L = S.Line(contraction.E)
        tangent = L - sum(e for e in E_on_tangent)
        conic = 2*L - sum(e for e in E_on_conic)
        fibers = [2*L - sum(E_on_fiber) for E_on_fiber in E_on_fibers]
        #fibers containing at least two Ei
        special_fibers = [E_on_fiber for E_on_fiber in E_on_fibers if len(E_on_fiber)>1]

        for e in contraction.E:
            if S.dot(e,tangent)==0 and S.dot(e,conic)==0 and all(S.dot(e,fiber)==0 for fiber in E_on_fibers):
                fibers.append(2*L - e)
        pol_gens = list(contraction.contracted_curves) + [conic, tangent] + fibers
        assert all(S.dot(c,e)<=1 for c in pol_gens for e in contraction.E)


        # the dimension of the linear system of possible conics Q
        dim_Q = 5 - len(E_on_conic)
        # the dimension of the linear system of possible lines T (before the tangency condition)
        dim_T = 2 - len(E_on_tangent)

        if dim_Q<0 or dim_T<0:
            raise ValueError('No cylinders exist')

        # now we compute parameters for the moduli of (Q,T) with tangency condition

        intersection_QT = [e for e in E_on_conic if e in E_on_tangent]
        if len(intersection_QT)>2:
            raise ValueError('Q and T have more than double intersection point')
        elif len(intersection_QT)==2:
            QT_is_linear = True
            QT_dimension = dim_Q + dim_T
        else:
            QT_is_linear = False
            QT_dimension = dim_Q + dim_T - 1

        for fiber in special_fibers:
            QT_dimension -= len(fiber) - 1
            QT_is_linear = False

        if QT_dimension<0:
            raise ValueError('No cylinders exist')     
        transversal = QT_dimension > 0 or not QT_is_linear
        forb_gens = pol_gens if transversal else [c for c in pol_gens if c!=tangent]

        # checks if there are at least two tangents through a given point. 
        two_tangents_through_point = len(E_on_tangent)<=1 and all(len(E_on_fiber)<=1 for E_on_fiber in E_on_fibers)<=1
        # there are at least two tangents such that there is a fiber containing two given points, see CPW Th.6.2.3
        two_tangents_with_fiber_through_two_points = len(E_on_tangent)==0 and len(special_fibers)<=1 and all(len(E_on_fiber)<=2 for E_on_fiber in special_fibers)
        if two_tangents_through_point or two_tangents_with_fiber_through_two_points:            
            assert transversal == True

        return cls.make(S, forb_gens, pol_gens, 2*L, construction='tangent', transversal=transversal, dimension = QT_dimension)

    @classmethod
    def make_type_tangent2(cls, S:Surface, E:list[Curve], E_on_conic:Sequence[Curve])->'Cylinder':
        '''
        See Perepechko-2013 Section 4.1. 
        We draw a conic through blown up points at E_small and take a generic tangent line. 
        Technically, we obtain a collection of cylinders with no common fibers.
        '''
        assert len(E_on_conic)<=5
        return cls.make_type_tangent(S, E, E_on_conic, [], [[e] for e in E if e not in E_on_conic])


    @classmethod
    def make_type_P1xP1(cls, S:Surface, E:list[Curve], Ei,Ej)->'Cylinder':
        '''
        Cheltsov-Park-Won Example 4.1.6 and Lemma 4.2.2 for contraction of E1..E4, L-E5-E6 in degree 3. See also Perepechko Ex. 5.3.
        This is again a pair of cylinders without common fibers.
        #TODO can we use it for degree 2?
        '''
        assert S.degree<=7  and S.degree>=3 
        assert Ei in E and Ej in E and Ei!=Ej
        L = S.Line(E)
        E_complement = [e for e in E if (e!=Ei) and (e!=Ej)]
        conic = -S.K-L+Ei
        complement = [e for e in E_complement]+[L-Ei-Ej, conic]
        support = complement + [L-Ei,L-Ej]
        return cls.make(S, complement, support, None, construction='P1xP1')

    @classmethod
    def make_type_cuspcubic(cls, S:Surface, E:list[Curve], E_small:Sequence[Curve])->'Cylinder':
        '''
        See Cheltsov-Park-Won Ex.4.1.13 and Th.6.2.2 case 2.
        C is an anticanonical cuspidal curve, cubic on contraction to P^2 defined by (E minus E_small) and M.
        We assume that there are at least two such curves (with distinct cusp points).
        E_small defines the contraction from degree 5.
        '''
        assert S.degree >= 2  and S.degree <= 5
        assert len(E_small) == 4 and all(e in E for e in E_small)
        L = S.Line(E)
        C = - S.K
        M = [2*L-sum(E_small)] + [L-e for e in E_small]        
        complement =  [e for e in E if e not in E_small] 
        support = [C] + M + complement
        fiber = 2*C
        return cls.make(S, complement, support, fiber, construction='cuspcubic', transversal=True)


    @classmethod
    def make_type_cuspcubic2(cls, S:Surface, E:list[Curve], E_small:Sequence[Curve])->'Cylinder':
        #TODO adapt for degree <=5
        '''
        See Cheltsov-Park-Won Ex.4.1.11.
        '''
        assert S.degree == 2 
        assert len(E_small) == 4 
        L = S.Line(E)
        C = 3 *L-sum(E)
        M = [2 *L-sum(E_small)] + [L-e for e in E_small]
        support = [C] + M + E
        complement = E
        return cls.make(S, complement, support, None, construction='cuspcubic')

    @classmethod
    def make_type_cuspcubic_L12(cls, S:Surface, E:list[Curve], E_on_line:Sequence[Curve])->'Cylinder':
        '''
        See Cheltsov-Park-Won Th.6.2.2, Case 2.4
        '''
        assert S.degree >= 2 and S.degree <= 7
        assert len(E_on_line) == 2 and all(e in E for e in E_on_line)
        E_other = [e for e in E if e not in E_on_line]
        L = S.Line(E)
        C = 3 *L-sum(E)
        L12 = L - sum(E_on_line)
        F = [L-e for e in E_on_line]
        complement = E_other + [L12]
        support = complement + [C] + F
        return cls.make(S, complement, support, 2*(F[0]+F[1]), construction='cuspcubic')


    @cached_property
    def Pol(self):
        return Cone(self.support)

    @cached_property
    def Forb(self):
        return Cone(self.complement)

    def is_polar_on(self, cone:ConvexRationalPolyhedralCone|str):
        if isinstance(cone, str):
            cone = NE_SubdivisionCone.representative(self.S, cone).cone
        return relint_contains_relint(self.Pol, cone)
    
    def is_complete_on(self, cone:ConvexRationalPolyhedralCone, exclude:ConvexRationalPolyhedralCone|None=None):
        '''
        checks if the collection is H-complete for ample divisor classes H from the relative interior of cone
        exclude is a cone of divisors to be excluded from completeness check
        '''
        intersection = cone.intersection(self.Forb)
        if not relint_contains_relint(cone, intersection):
            return True
        if exclude == None:
            return False
        forb_intersection_excluded = all(exclude.contains(ray) for ray in intersection.rays())
        return forb_intersection_excluded

    def is_transversal(self):
        if self.transversal!=None: 
            return self.transversal 
        return self.fiber == None

    def compatible_representatives(self, complete=False) -> Iterable[str]:
        '''
        yields types of representatives, on which self is polar and, optionally, complete
        '''
        types = NE_SubdivisionCone.cone_types(self.S)
        for t in types:
            #print(f'looking at type {t}')
            cone = NE_SubdivisionCone.representative(self.S, t).cone
            if self.is_polar_on(cone):
                if complete and not self.is_complete_on(cone):
                    continue
                yield t

    # def latex(self) -> str:
    #     result = \
    #         f'''
    #         construction: {self.construction}
    #         used contraction: {self.S._curves_name(self.contraction.contracted_curves)}
    #         pencil generators: {self.S._curves_name(self.pencil_generators)}
    #         generic fiber: {self.fiber}
    #         polarity cone generators: {self.S._curves_name(self.support)}
    #         forbidden cone generators: {self.S._curves_name(self.complement)}
    #         is transversal: {self.transversal}
    #         '''
            
    #     return result


class CylinderList(list):
    '''
    A list of cylinders with extra info.

    complement is the list of (-1)-curves lying in the complement of the cylinders' union
    fiber is the generic fiber class of the collection. If the collection is transversal, then the fiber is empty
    '''

    def __init__(self, cylinders:Iterable[Cylinder], S:Surface|None=None) -> None:
        super().__init__(cylinders)
        if len(self)==0  and S==None:
            raise ValueError('The surface is not defined')
        self.S = S if S!=None else self[0].S
        for cyl in self:
            self._validate_cylinder(cyl)

    def __add__(self, other):        
        if self.S != other.S:
            raise ValueError('Different surfaces')
        cylinders = list(self) + list(other)
        return CylinderList(cylinders, self.S)
    
    def __setitem__(self, index, item):
        super().__setitem__(index, self._validate_cylinder(item))

    def copy(self)->'CylinderList':
        return CylinderList(super().copy(), self.S)

    def insert(self, index, item):
        print(super(), type(self))
        super().insert(index, self._validate_cylinder(item))

    def append(self, item):
        super().append(self._validate_cylinder(item))

    def extend(self, other):
        if isinstance(other, type(self)):
            if self.S != other.S:
                raise ValueError('Different surfaces')
            super().extend(other)
        else:
            super().extend(self._validate_cylinder(item) for item in other)

    def _validate_cylinder(self, cylinder) -> Cylinder:
        if not isinstance(cylinder, Cylinder):
            #print(type(cylinder), cylinder.S)
            raise TypeError(f'{cylinder} is not a Cylinder')
        if cylinder.S != self.S:
            raise ValueError(f'{cylinder} is defined on other surface')
        return cylinder

    @cached_property
    def fiber(self):
        fiber = self[0].fiber
        if fiber!=None:
            if any(fiber!=cyl.fiber for cyl in self[1:]):
                return None
        return fiber
        
        
    @cached_property
    def complement(self):
        if len(self)==0:
            raise ValueError('The collection is empty, complement curves are undefined')
            return self.S.minus_one_curves
        complement = [curve for curve in self[0].complement if all(curve in cyl.complement for cyl in self[1:])]
        return complement
        
    @cached_property
    def complement_double_points(self):
        return [p for p in self.S.double_intersections if all(p in curve for curve in self.complement)]
    
    @cached_property
    def Pol(self):
        #TODO ensure that the dimension of cone does not change
        result = Cone([],lattice=self.S.N.dual()).dual() # ambient space
        for cylinder in self:
            result = result.intersection(cylinder.Pol)
        interior_element = sum(result.rays())
        if all(c.Pol.relative_interior_contains(interior_element) for c in self):
            return result
        else:
            return Cone([],lattice=self.S.N)

    @cached_property #TODO if it is rarely invoked, then we should not cache the result. Are there tests for memory usage?
    def Forb(self):
        if len(self) == 0 :
            return Cone([],lattice=self.S.N.dual()).dual()
        return Cone(self.complement, lattice=self.S.N)

    def is_polar_on(self, cone:ConvexRationalPolyhedralCone|str) -> bool:
        '''
        cone is either a Cone or a type of cone, which would be converted to a representative
        '''
        if isinstance(cone, str):
            cone = NE_SubdivisionCone.representative(self.S, cone).cone
        return relint_contains_relint(self.Pol, cone)

    def get_polar_on(self, cone:ConvexRationalPolyhedralCone|str, restrict_to_ample:bool=True) -> 'CylinderList':
        '''
        return a  sublist of cylinders that are polar on the given cone 
        
        INPUT:
        cone is either a Cone or a type of cone, which would be converted to a representative
        '''
        if isinstance(cone, str):
            cone = NE_SubdivisionCone.representative(self.S, cone).cone
        if restrict_to_ample:
            cone = cone.intersection(self.S.Ample)
        cylinders = [c for c in self if c.is_polar_on(cone)]
        return CylinderList(cylinders, self.S)

    def reduce(self, keep_double_points:bool=False) -> 'CylinderList':
        '''
        keep_double_points is a boolean that indicates whether double points in the union of cylinders should be preserved
        '''
        if keep_double_points:
            raise NotImplementedError
        cylinders_count = Counter()
        removed_cylinders = set()
        for cylinder in self:
            if all(cylinders_count[curve]>0  for curve in cylinder.complement):
                removed_cylinders.add(cylinder)
                continue
            cylinders_count.update(cylinder.complement)
        while True:
            for cyl in self:
                if cyl in removed_cylinders:
                    continue
                if all(cylinders_count[curve]>1  for curve in cyl.complement):
                    removed_cylinders.add(cyl)
                    for curve in cyl.complement:
                        cylinders_count[curve]-=1 
                    break
            else:
                break
        return CylinderList([c for c in self if c not in removed_cylinders], self.S)
        #TODO implement this for double (triple) points, some old code below
        if len(complement_points(collection)['double'])!=0 :
            print('this collection does not cover all double points')
            return collection
        print('deleting cylinders, remaining:')
        while True:
            for i in range(len(collection)):
                collection_without_cylinder = collection[:i] + collection[i+1 :]
                if len(complement_points(collection_without_cylinder)['double'])==0 :
                    del collection[i]
                    print(len(collection), end=' ')
                    break
            else:
                print('no cylinders to delete')
                break
        return collection

    def is_transversal(self):
        if any(cyl.transversal == True for cyl in self):
            return True
        if self.fiber == None:
            return True
        if len(self) == 0:
            return False
        basepoint = self[0].basepoint
        if basepoint == None:
            return False
        return any(basepoint != cyl.basepoint for cyl in self[1:])

    
    def is_complete_on(self, cone:ConvexRationalPolyhedralCone, exclude:ConvexRationalPolyhedralCone|None=None):
        '''
        checks if the collection is H-complete for ample divisor classes H from the relative interior of cone
        exclude is a cone of divisors to be excluded from completeness check
        '''
        intersection = cone.intersection(self.Forb)
        if not relint_contains_relint(cone, intersection):
            return True
        if exclude == None:
            return False
        forb_intersection_excluded = all(exclude.contains(ray) for ray in intersection.rays())
        return forb_intersection_excluded


    def is_generically_flexible_on(self, cone:ConvexRationalPolyhedralCone|str, exclude:ConvexRationalPolyhedralCone|str|None=None, restrict_to_ample:bool=True)->bool:
        '''
        checks if the collection provides generic flexibility for ample divisors in the provided cone
        exclude is a cone of divisors to be excluded from completeness check
        '''
        if isinstance(cone, str):
            cone = NE_SubdivisionCone.representative(self.S, cone).cone
        if isinstance(exclude, str):
            exclude = NE_SubdivisionCone.representative(self.S, cone).cone
        if restrict_to_ample:
            cone = cone.intersection(self.S.Ample)
            if not relint_contains_relint(self.S.Ample, cone):
                return True
        is_polar = self.is_polar_on(cone)
        is_complete = self.is_complete_on(cone, exclude)
        return is_polar and is_complete and self.is_transversal()
    
    def __str__(self) -> str:
        return f'Cylinder collection with {len(self)} cylinders on {self.S}'
        


class CylinderGenerator:
    
    @classmethod
    def make_cylinder_QT(cls, S, E_on_conic:Sequence[ToricLatticeElement], E_on_tangent:Sequence[ToricLatticeElement], E_on_fibers: list[Sequence[ToricLatticeElement]]|None = None)->'Cylinder':  
        return Cylinder.make_type_tangent_weak(S.S, S, E_on_conic, E_on_tangent, E_on_fibers)

    @classmethod
    def find_cylinders_LL(cls, S)->Generator['Cylinder',None,None]:
        for L1, dim_1 in S.line_classes:
            for L2, dim_2 in S.line_classes:
                intersection = [S._E_to_C(e) for e in S.E if S.S.dot(e,L1)==1 and S.S.dot(e,L2)==1]
                if len(intersection)>1:
                    continue
                base_curves = [chain[0] for chain in S.chains_of_contracted_curves]
                curves_on_other_fibers = [c for c in base_curves if S.S.dot(S._C_to_E(c),L1+L2)==0]
                complement = list(S.C)
                # we don't check the case when, say, fibers L12, L34 and L56 intersect in the same point (i.e., Echkardt point). Indeed, this case is automatically covered when generic flexibility is in question
                support = list(S.C) + [L1, L2] + [S.L- S._C_to_E(c) for c in curves_on_other_fibers]
                if dim_1 == 0:
                    complement.append(L1)
                if dim_2 == 0:
                    complement.append(L2)
                dimension = dim_1 + dim_2 if len(intersection) == 0 else 0
                transversal = dimension>0 

                basepoint = Point(frozenset([L1,L2])) if len(intersection)==0 else None
                yield Cylinder.make(S.S, 
                                         construction='lines',
                                         contraction=S,
                                         pencil_generators=(L1,L2),
                                         complement=complement, 
                                         support=support, 
                                         fiber=2*S.L - sum(intersection), 
                                         basepoint=basepoint,
                                         transversal=transversal,
                                         dimension=dimension)

    @classmethod
    def find_cylinders_QT(cls, S)->Generator['Cylinder',None,None]:
        labels = ['Q','T','QT','F1','F2','F3','F4']
        #TODO remove configs?
        empty_config = {c:'' for c in S.C}
        for Q, dim_Q in S.conic_classes:
            for T, dim_T in S.line_classes:
                config = empty_config.copy()
                QT_is_linear = True
                for c in S.C: 
                    e = S._C_to_E(c)
                    if S.S.dot(e,Q) == 1:
                        config[c] = 'Q'
                    if S.S.dot(e,T) == 1:
                        config[c] += 'T'
                intersection = [c for c,v in config.items() if v=='QT']                
                dim_QT = dim_Q + dim_T
                # if(dim_QT<=2):
                #     ic(Q,T, config, dim_Q, dim_T, intersection)
                if len(intersection)>2:
                    continue
                elif len(intersection)==2:
                    c1,c2 = intersection
                    if S.S.dot(c1,c2) != 1:
                        continue
                elif len(intersection) == 1:
                    c = intersection[0]
                    c_neighours = [d for d in S.C if S.S.dot(d,c)==1]
                    if len(c_neighours)==1 and config[c_neighours[0]]!='':
                            continue
                    dim_QT -= 1
                else:
                    dim_QT -= 1
                    QT_is_linear = False
                
                if dim_QT < 0:
                    continue

                transversal = dim_QT > 0 or not QT_is_linear
                complement = list(S.C)
                support = complement + [Q, T]                
                if dim_Q == 0:
                    complement.append(Q)
                    if dim_QT == 0 and QT_is_linear:
                        complement.append(T)
                elif dim_T == 0:
                    complement.append(T)
                #TODO special fibers

                basepoint = Point(frozenset([Q,T])) if len(intersection)==0 else None
                yield Cylinder.make(S.S, 
                                         complement=complement, 
                                         support=support, 
                                         construction='tangent',
                                         contraction=S,
                                         pencil_generators=(Q,T),
                                         fiber=2*S.L - sum(intersection), 
                                         basepoint=basepoint,
                                         transversal=transversal,
                                         dimension=dim_QT)


    @classmethod
    def cylinders(cls, S, E, construction:str) -> Iterable['Cylinder']:
        '''
        S is the studied surface
        E is the list of exceptional curves of a blowdown to P2
        constructions is the list of names of methods to construct cylinders
        '''
        #TODO check each for arbitrary degree
        match construction:
            case 'lines':
                for e in E:
                    yield Cylinder.make_type_lines(S, E, e)
            case 'lines2':
                if S.degree <= 5:
                    for e1,e2,e3,e4 in itertools.combinations(E,int(4 )):
                        yield Cylinder.make_type_lines2(S, E, e1, e2, e3, e4)
                        yield Cylinder.make_type_lines2(S, E, e1, e3, e2, e4)
                        yield Cylinder.make_type_lines2(S, E, e1, e4, e2, e3)
            case 'tangent':
                if S.degree >= 3:  
                    for e in E:    
                        yield Cylinder.make_type_tangent(S, E, E_on_conic=[f for f in E if f!=e], E_on_tangent=[e])
            case 'P1xP1': 
                if S.degree <= 7  and S.degree >= 3 :
                    for Ei,Ej in itertools.permutations(E, int(2 )):
                        yield Cylinder.make_type_P1xP1(S, E, Ei, Ej)
            case 'cuspcubic':
                if S.degree == 2 :
                    for E_small in itertools.combinations(E,int(4 )):
                        yield Cylinder.make_type_cuspcubic(S, E, E_small)

    @classmethod
    def all_cylinders(cls, S: Surface, constructions: list[str]) -> Generator[Cylinder, None, None]:
        for contraction in S.contractions_P2():
            for construction in constructions:
                yield from cls.cylinders(S, contraction.E, construction)
    
