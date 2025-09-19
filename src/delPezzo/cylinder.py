from typing import Iterable, Sequence, Generator
from dataclasses import dataclass
import itertools
from functools import cached_property
from collections import Counter

from sage.geometry.cone import ConvexRationalPolyhedralCone, Cone
from sage.geometry.toric_lattice import ToricLatticeElement

from delPezzo.surface import Surface, Curve, Point
#from .cone import NE_SubdivisionCone, relint_contains_relint
from delPezzo.contraction import Contraction, ContractionToPlane, candidate_zero_curves
from delPezzo.surface2 import Stratum, Surface2


@dataclass
class Pencil:
    '''
    a pencil with rational irreducible fibers and at most one base point.

    We assume that the fibers are smooth outside of the basepoint
    '''
    S: Surface2
    pic_class: ToricLatticeElement
    basepoint_locus: Stratum|None

    def __post_init__(self):
        self.pic_class.set_immutable()

    def curves_in_fibers(self) -> list[Curve]:
        '''
        return negative curves in the element of self

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> P = Pencil(S, S.N([1,-1,0,0]))
            >>> P.curves_in_fibers()
            [E_1, E_2, E_3, E_4]
        '''
        return [c for c in self.S.neg_curves if c.dot(self.pic_class)<0]




@dataclass(frozen=True)
class Cylinder:
    '''

    Attributes:
      - `fiber` is the generic fiber class of the cylinder (or cylinders if several). If the collection is transversal, then the fiber is empty.
      - `complement` is the list of (-1)-curves lying in the complement of the cylinders' union
      - `support` is the list of (-1)-curves lying in the support of divisors, where the cylinders' union is polar
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

    @cached_property
    def Pol(self):
        return Cone(self.support)

    
    def is_polar_on(self, cone:ConvexRationalPolyhedralCone):
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

    @property
    def fiber(self):
        fiber = self[0].fiber
        if fiber!=None:
            if any(fiber!=cyl.fiber for cyl in self[1:]):
                return None
        return fiber
        
        
    @property
    def complement(self):
        if len(self)==0:
            raise ValueError('The collection is empty, complement curves are undefined')
            return self.S.minus_one_curves
        complement = [curve for curve in self[0].complement if all(curve in cyl.complement for cyl in self[1:])]
        return complement
        
    @property
    def complement_double_points(self):
        return [p for p in self.S.double_intersections if all(p in curve for curve in self.complement)]
    
    @property
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

    @property #TODO never cache, since list changes
    def Forb(self):
        if len(self) == 0 :
            return Cone([],lattice=self.S.N.dual()).dual()
        return Cone(list(self.complement) + [-c for c in self.complement], lattice=self.S.N)

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
    def from_zero_classes(cls, C:ContractionToPlane)->'Generator[Cylinder,None,None]':
        '''
        return cylinders that come from P1-fibrations on the surface `C.src`
        
        '''
        S = C.src
        curves = [c for c in candidate_zero_curves(S.degree) if all(S.dot(e,c)>=0 for e in S.neg_curves)]
        for curve in curves:
            reducible_fibers = [c for c in S.neg_curves if S.dot(c, curve) < 0]
            for e in S.neg_curves:
                if S.dot(e, curve) == 1:
                    yield Cylinder.make(
                        S=          S, 
                        complement= reducible_fibers+[e], 
                        support=    reducible_fibers+[e], 
                        fiber=      curve,
                        construction='fibration',
                        transversal=False,
                        dimension=1,
                        )        
