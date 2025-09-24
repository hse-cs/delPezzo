
@dataclass(frozen=True)
class Pencil:
    '''
    a pencil with rational irreducible fibers and at most one base point.

    We assume that the fibers are smooth outside of the basepoint
    '''
    S: Surface
    pic_class: ToricLatticeElement
    basepoint_locus: Stratum|None = None
    check: bool = True

    def __post_init__(self):
        self.pic_class.set_immutable()
        if self.check and not self._check():
            raise ValueError(f'{self} is not valid')

    @cached_property
    def curves_in_fibers(self) -> tuple[Curve,...]:
        '''
        return negative curves in the element of self

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> Pencil(S, S.N([1,-1,0,0])).curves_in_fibers
            (L_{123}, E_2, E_3)
        '''
        return tuple(c for c in self.S.neg_curves if c.dot(self.pic_class)==0)

    def _check(self) -> bool:
        '''
        check some correctness conditions

        namely, a zero class has no basepoint and vice versa; negative class is impossible; no fixed component present (i.e., is nef)
        
        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> Pencil(S, S.N([1,-1,0,0]))._check()
            True
            >>> Pencil(S, S.N([1,-1,-1,0]),check=False)._check()
            False
            >>> Pencil(S, S.N([1,0,0,0]),check=False)._check()
            False
            >>> Pencil(S, S.N([1,0,0,0]), Stratum([]))._check()
            True
            >>> Pencil(S, S.N([1,0,0,0]), Stratum([S.curve("E_1")]),check=False)._check()
            False
        '''
        
        if any(self.S.dot(c,self.pic_class)<0 for c in self.S.NE_gens):
            return False

        self_intersection = self.S.dot(self.pic_class, self.pic_class)
        if self_intersection < 0:
            return False
        elif self_intersection == 0:
            return self.basepoint_locus is None
        else:
            if self.basepoint_locus is None:
                return False 
            return all(c.dot(self.pic_class)>0  for c in self.basepoint_locus.curves)

    def is_fibration(self) -> bool:
        '''
        check if self is a fibration (i.e., elements are disjoint)

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> Pencil(S, S.N([1,-1,0,0])).is_fibration()
            True
            >>> Pencil(S, S.N([1,0,0,0]), Stratum([])).is_fibration()
        '''
        return self.basepoint_locus is None
    


@dataclass(frozen=True)
class Cylinder(Pencil):
    '''
    a class of a cylinder

    if the pencil is a fibration, then we need to specify a section curve; we restrict to negative sections
    '''
    section : Curve|None = None

    def _check(self) -> bool:
        '''
        check some necessary conditions

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> Cylinder(S, S.N([1,-1,0,0]),check=False)._check()
            False
            >>> Cylinder(S, S.N([1,-1,0,0]),section=S.curve("E_1"))._check()
            True
        '''
        if not super()._check():
            return False
        if self.is_fibration():
            if self.section is None:
                return False
            if self.S.dot(self.pic_class, self.section)!=1:
                return False

        #TODO check that fibers are rational, irreducible, smooth?
        return True

    @cached_property
    def complement(self) -> tuple[Curve,...]:
        '''
        return negative curves in the complement of self
        
        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> Cylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),)).complement
            (L_{123}, E_2, E_3, E_1)
        '''
        if self.section is None:
            return self.curves_in_fibers
        else:
            return self.curves_in_fibers + (self.section,)

    @cached_property
    def Pol(self) -> Cone_relint:
        '''
        return the cone of Q-divisors H such that self is H-polar

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> cyl = Cylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),))
            >>> cyl.Pol().contains_relint(S.N([1,0,0,0]))
            True
        '''
        return Cone_relint(self.complement)

    def is_polar_on(self, other:Cone_relint|ToricLatticeElement):
        '''
        check if self is polar on divisor classes in other

        TESTS:
            >>> S = Surface2(6,[[1,-1,-1,-1]])
            >>> cyl = Cylinder(S, S.N([1,-1,0,0]),section=(S.curve("E_1"),))
            >>> cyl.is_polar_on(S.N([1,0,0,0]))
            True
        '''
        return self.Pol().contains_relint(other)
    
    # def is_complete_on(self, cone:ConvexRationalPolyhedralCone, exclude:ConvexRationalPolyhedralCone|None=None):
    #     '''
    #     checks if the collection is H-complete for ample divisor classes H from the relative interior of cone
    #     exclude is a cone of divisors to be excluded from completeness check
    #     '''
    #     intersection = cone.intersection(self.Forb)
    #     if not relint_contains_relint(cone, intersection):
    #         return True
    #     if exclude == None:
    #         return False
    #     forb_intersection_excluded = all(exclude.contains(ray) for ray in intersection.rays())
    #     return forb_intersection_excluded

