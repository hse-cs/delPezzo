from typing import Any, Iterable, Self, Sequence, Generator, SupportsIndex, override
from dataclasses import dataclass
import itertools
from functools import cached_property
from collections import Counter
from abc import ABC, abstractmethod

from delPezzo.cone import Cone_relint
from numpy import isin
from sage.geometry.cone import ConvexRationalPolyhedralCone, Cone
from sage.geometry.toric_lattice import ToricLatticeElement

from delPezzo.surface import Surface, Curve, Point
#from .cone import NE_SubdivisionCone, relint_contains_relint
from delPezzo.contraction import Contraction, ContractionToPlane, candidate_zero_curves
from delPezzo.surface2 import Stratum, Surface2


class PreCylinder(ABC):
    '''
    a precylinder is a collection of cylinders that are equivalent in some way
    '''
    @property
    @abstractmethod
    def S(self) -> Surface:
        '''
        return the surface this precylinder is on
        '''
        ...

    @property
    @abstractmethod
    def pic_class(self) -> ToricLatticeElement:
        '''
        return the class of a general cylinder fiber 
        '''
        ...

    @abstractmethod
    def _check(self) -> bool:
        ...

    @cached_property
    def complement(self) -> list[Curve]:
        '''
        return the complement to the precylinder
        '''
        return self._complement()

    @abstractmethod
    def _complement(self) -> list[Curve]:
        ...

    @abstractmethod
    def Pol(self) -> Cone_relint:
        '''
        return the polarity cone
        '''
        ...

    def is_polar_on(self, cone:ConvexRationalPolyhedralCone) -> bool:
        '''
        check if self is polar on the relative interior of the given cone
        '''
        return self.Pol().contains_relint(cone)

@dataclass(frozen=True)
class FibrationCylinder(PreCylinder):
    _S: Surface
    zero_class: ToricLatticeElement
    section: Curve
    check: bool = True


    def __post_init__(self):
        self.zero_class.set_immutable()
        if self.check and not self._check():
            raise ValueError(f'{self} is not valid')

    def _check(self) -> bool:
        '''
        check some necessary conditions

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> FibrationCylinder(S, S.N([1,-1,0,0]),section=S.curve("E_2"),check=False)._check()
            False
            >>> FibrationCylinder(S, S.N([1,-1,0,0]),section=S.curve("E_1"))._check()
            True
        '''
        # zero class
        if self.S.dot(self.pic_class, self.pic_class)!=0:
            return False                
        # section
        if self.S.dot(self.pic_class, self.section)!=1:
            return False
        # nef
        if not all(self.S.dot(c,self.pic_class)>0 for c in self.S.NE_gens): 
            return False 
        # rational
        if self.S.dot(self.S.K, self.pic_class)!=-2:
            return False
        return True

    def curves_in_fibers(self) -> tuple[Curve,...]:
        '''
        return negative curves in the element of self

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> FibrationCylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),)).curves_in_fibers
            (L_{123}, E_2, E_3)
        '''
        return tuple(c for c in self.S.neg_curves if c.dot(self.pic_class)==0)


    @property
    def S(self) -> Surface:
        return self._S

    @property
    def pic_class(self) -> ToricLatticeElement:
        return self.zero_class

    def _complement(self) -> list[Curve]:
        return [self.section] + list(self.curves_in_fibers())
    
    def Pol(self) -> Cone_relint:
        '''
        return the cone of Q-divisors H such that self is H-polar

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> cyl = FibrationCylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),))
            >>> cyl.Pol().contains_relint(S.N([1,0,0,0]))
            True
        '''
        return Cone_relint(self.complement)

    def is_minimal(self) -> bool:
        '''
        check if self cannot be reduced to a contraction
        '''
        return all(c.dot(c)!=-1 for c in self.curves_in_fibers())

@dataclass(frozen=True)
class FibrationCylinderImage(PreCylinder):
    contraction: Contraction
    fibration: FibrationCylinder
    check: bool = True


    def __post_init__(self):
        if self.check and not self._check():
            raise ValueError(f'{self} is not valid')

    def _check(self) -> bool:
        if not self.fibration._check():
            return False
        if self.contraction.src != self.fibration.S:
            return False
        return True

    @property
    def S(self) -> Surface:
        return self.contraction.dest
    

    def _complement_images(self) -> list[Curve]:
        '''
        classes of images of curves in the complement of the fibration
        '''
        return [self.contraction(c) for c in self.fibration.complement]

    def _complement(self) -> list[Curve]:
        '''
        the complement consists of images of curves that stayed negative
        '''
        return [c for c in self._complement_images() if self.S.dot(c,c) < 0]

    def Pol(self) -> Cone_relint:
        '''
        return the polarity cone
        '''
        return Cone_relint(self._complement_images())

    @property
    def pic_class(self) -> ToricLatticeElement:
        return self.contraction(self.fibration.pic_class)

    #TODO Why do we have one?
    def basepoint_locus(self) -> Stratum|None:
        neg_curves_meeting_section = [c for c in self.contraction.src.neg_curves if self.contraction.src.dot(c, self.fibration.section) == 0]
        negative_images = [self.contraction(c) for c in neg_curves_meeting_section if self.S.dot(c,c) < 0]
        return Stratum(tuple(negative_images))

class CylinderList(list[PreCylinder]):
    '''
    A list of cylinders with extra info.
    '''

    def __init__(self, cylinders:Iterable[PreCylinder], S:Surface|None=None, check:bool=True) -> None:
        super().__init__(cylinders)
        if len(self)==0  and S==None:
            raise ValueError('The surface is not defined')
        self.S = S if S!=None else self[0].S
        if check:
            self._check()


    def _check(self) -> bool:
        return all(cyl._check() for cyl in self)

    def _check_cylinder(self, cylinder:PreCylinder) -> PreCylinder:
        '''
        check if precylinder is on the correct surface
        '''
        if not isinstance(cylinder, PreCylinder):
            #print(type(cylinder), cylinder.S)
            raise TypeError(f'{cylinder} is not a PreCylinder')
        if cylinder.S != self.S:
            raise ValueError(f'{cylinder} is defined on another surface')
        return cylinder
    
    #TODO failed to add type hints. Solution: turn into dataclass with fields cylinders, S (and inherit from MutableSequence?). Or inherit from collections.UserList .
    def __add__(self, other) -> 'CylinderList':
        '''
        join two lists

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> cyl1 = FibrationCylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),))
            >>> cyl2 = Cylinder(S, S.N([1,0,0,0]),basepoint_locus=Stratum([]))
            >>> len(CylinderList([cyl1]) + CylinderList([cyl2]))
            2
        '''
        if self.S != other.S:
            raise ValueError('Different surfaces')
        cylinders = list(self) + list(other)
        return CylinderList(cylinders, self.S)



    # def __setitem__(self, key, value):
    #     '''
    #     set self[key] to value with additional check
        
    #     TESTS:
    #         >>> S = Surface2(6,[[1,-1,-1,-1]])
    #         >>> cyl1 = Cylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),))
    #         >>> cyl2 = Cylinder(S, S.N([1,0,0,0]),basepoint_locus=Stratum([]))

    #     '''
    #     super().__setitem__(key, self._check_cylinder(value))

    def copy(self)->'CylinderList':
        '''
        return a copy of self
        
        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> cyl1 = Cylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),))
            >>> clist = CylinderList([cyl1]); copy = clist.copy()
            >>> (clist == copy) and (not clist is copy)
            True
        '''
        return CylinderList(super().copy(), self.S)

    # def insert(self, index, item):
    #     #print(super(), type(self))
    #     super().insert(index, self._check_cylinder(item))

    # def append(self, item):
    #     super().append(self._check_cylinder(item))

    # def extend(self, other):
    #     if isinstance(other, type(self)):
    #         if self.S != other.S:
    #             raise ValueError('Different surfaces')
    #         super().extend(other)
    #     else:
    #         super().extend(self._check_cylinder(item) for item in other)
        
        
    def complement(self) -> list[Curve]:
        '''
        return list of negative curves lying in the complement of all items

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> cyl1 = Cylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),))
            >>> cyl2 = Cylinder(S, S.N([1,0,0,0]),basepoint_locus=Stratum([]))
            >>> CylinderList([cyl1,cyl2]).complement()
            [E_2, E_3, E_1]
        '''
        if len(self)==0:
            raise ValueError('The collection is empty, complement curves are undefined')
        complement = [curve for curve in self[0].complement if all(curve in cyl.complement for cyl in self[1:])]
        return complement
        
    # @property
    # def complement_double_points(self):
    #     return [p for p in self.S.double_intersections if all(p in curve for curve in self.complement)]
    
    def Pol(self) -> Cone_relint:
        '''
        return the cone of Q-divisors H such that all cylinders in self are H-polar
        
        '''
        #TODO ensure that the dimension of cone does not change
        result = Cone([],lattice=self.S.N.dual()).dual() # ambient space
        for cylinder in self:
            result = result.intersection(cylinder.Pol)
        interior_element = sum(result.rays())
        if all(c.Pol().contains_relint(interior_element) for c in self):
            return Cone_relint(result)
        else:
            return Cone_relint(Cone([],lattice=self.S.N))
            #TODO introduce empty Cone_relint with overridden "contains_relint"

    def Forb(self) -> ConvexRationalPolyhedralCone:
        '''
        return the forbidden cone
        
        TESTS:
        '''
        if len(self) == 0:
            return Cone([],lattice=self.S.N.dual()).dual()
        complement = self.complement()
        if len(complement) == 0:
            return Cone([],lattice=self.S.N)
        opposite_vector = - sum(complement) # the Forb is actually a subspace?
        return Cone(list(complement) + [opposite_vector], lattice=self.S.N)

    def is_polar_on(self, cone:ConvexRationalPolyhedralCone) -> bool:
        '''
        cone is either a Cone or a type of cone, which would be converted to a representative
        '''
        return self.Pol().contains_relint(cone)

    def get_polar_on(self, cone:ConvexRationalPolyhedralCone, restrict_to_ample:bool=True) -> 'CylinderList':
        '''
        return a  sublist of cylinders that are polar on the given cone 
        
        INPUT:
        cone is either a Cone or a type of cone, which would be converted to a representative
        '''
        if restrict_to_ample:
            cone = cone.intersection(self.S.Ample)
        cylinders = [c for c in self if c.is_polar_on(cone)]
        return CylinderList(cylinders, self.S)

    def reduce(self) -> 'CylinderList':
        '''
        remove unnecessary cylinders
        '''
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

    def is_transversal(self):
        '''
        check if self is transversal

        
        '''
        if len(self) == 0:
            return False
        pic_class = self[0].pic_class
        if not all(c.pic_class == pic_class for c in self[1:]):
            return True
        if isinstance(self[0], FibrationCylinder):
            return False
        
        #if isinstance(self[0], FibrationCylinderImage):
        return False
        #TODO we should check further
        basepoint_locus = self[0].basepoint_locus
        if not all(c.basepoint_locus == basepoint_locus for c in self[1:]):
            return True
        if basepoint_locus is None:
            raise ValueError(f"Cylinder {self[0]} is not valid")
        return basepoint_locus.dim()>0


    def is_complete_on(self, cone:Cone_relint, exclude:ConvexRationalPolyhedralCone|None=None):
        '''
        check if the collection is H-complete for H from cone

        `exclude` is a cone of divisors to be excluded from completeness check
        '''
        intersection = cone.intersection(self.Forb)
        if not cone.contains_relint(intersection):
            return True
        if exclude == None:
            return False
        forb_intersection_excluded = all(exclude.contains(ray) for ray in intersection.rays())
        return forb_intersection_excluded


    def is_generically_flexible_on(self, cone:Cone_relint, exclude:ConvexRationalPolyhedralCone|str|None=None, restrict_to_ample:bool=True)->bool:
        '''
        checks if the collection provides generic flexibility for ample divisors in the provided cone
        exclude is a cone of divisors to be excluded from completeness check
        '''
        if restrict_to_ample:
            cone = cone.intersection(self.S.Ample)
            if not self.S.Ample.contains_relint(cone):
                return True
        is_polar = self.is_polar_on(cone)
        is_complete = self.is_complete_on(cone, exclude)
        return is_polar and is_complete and self.is_transversal()
    
    def __str__(self) -> str:
        return f'Cylinder collection with {len(self)} cylinders on {self.S}'
        

    @classmethod
    def from_zero_classes(cls, C:ContractionToPlane) -> Self:
        '''
        return cylinders that come from P1-fibrations on the surface `C.src`
        
        TESTS:
            >>> S=Surface(7); C=ContractionToPlane.of_curves(S, [S.curve(f"E_{i}") for i in range(1,3)])
            >>>  CylinderList.from_zero_classes(C)
        '''
        S = C.src
        curves = [c for c in candidate_zero_curves(S.degree) if all(S.dot(e,c)>=0 for e in S.neg_curves)]
        result = []
        for pic_class in curves:
            for section in [c for c in S.neg_curves if S.dot(c, pic_class) == 1]:
                result.append(Cylinder(
                    S=          S, 
                    pic_class=pic_class, 
                    section=section
                    ))
        return cls(result)


        #TODO descend fibrations by contracting sections and curves in fibers passing through basepoint


if __name__ == "__main__":
    import doctest
    doctest.testmod()


