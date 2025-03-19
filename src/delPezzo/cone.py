from sage.all_cmdline import *   # import sage library, otherwise other imports break #type: ignore
from sage.geometry.toric_lattice import ToricLatticeElement
from sage.geometry.cone import Cone, ConvexRationalPolyhedralCone, normalize_rays
from functools import cached_property, cache
import re
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Union

from .surface import Surface
#TODO make relint a class (dumb class over cone with set operators)


def relint_contains_relint(supercone: ConvexRationalPolyhedralCone,  cone: ConvexRationalPolyhedralCone) -> bool:
    '''
    checks if the relative interior of supercone contains the relative interior of cone
    '''
    contains_rays = all(supercone.contains(ray) for ray in cone.rays()) 
    relative_interiors_intersect = supercone.relative_interior_contains(sum(cone.rays()))
    return contains_rays and relative_interiors_intersect

def relints_intersect(cone1: ConvexRationalPolyhedralCone, cone2: ConvexRationalPolyhedralCone) -> bool:
    intersection = cone1.intersection(cone2)
    interior_ray = sum(intersection.rays())
    return cone1.relative_interior_contains(interior_ray) and cone2.relative_interior_contains(interior_ray)

@dataclass#(frozen=True)
class NE_SubdivisionCone:
    '''
    This class represents a cone obtained by subdivisions from NE and keeps the creation info.
    '''

    cone: ConvexRationalPolyhedralCone
    S: Surface
    parent: Union['NE_SubdivisionCone' , None] = None
    parent_face: ConvexRationalPolyhedralCone | None = None
    parent_ray: ToricLatticeElement | None = None

    @classmethod
    def NE(cls, S:Surface):
        cone = Cone(S.minus_one_curves + S.minus_two_curves + [S.L], lattice=S.N)
        return cls(cone=cone, S=S, parent=None, parent_face=None, parent_ray=None)

    @classmethod
    def from_face_and_ray(cls, parent:'NE_SubdivisionCone', face:ConvexRationalPolyhedralCone, ray:ToricLatticeElement):
        assert face.is_face_of(parent.cone)
        assert face != parent.cone
        rays = list(face.rays())+[ray]
        rays = sorted(normalize_rays(rays, parent.S.N))
        child_cone = Cone(rays, lattice=parent.S.N)
        ray.set_immutable()
        return cls(cone=child_cone, S=parent.S, parent=parent, parent_face=face, parent_ray=ray)
    
    def _members(self):
        return (self.cone, self.S, self.parent, self.parent_face, self.parent_ray) #TODO use hash(parent) instead to avoid recursion?

    def __eq__(self, other):
        if type(other) is type(self):
            return self._members() == other._members()
        else:
            return False

    def __hash__(self):
        if not hasattr(self, '_hash'):
            self._hash = hash(self._members())
        return self._hash
    

    def rays(self) -> Iterable[ToricLatticeElement]:        
        return self.cone.rays()
    
    def subdivision_faces(self, ray: ToricLatticeElement) -> Iterable[ConvexRationalPolyhedralCone]:
        '''
        returns faces of self that do not contain ray
        '''
        for faces_of_dim in self.cone.faces()[:-1]:
            for face in faces_of_dim:       # type: ignore
                if not face.contains(ray):  # type: ignore
                    yield face              # type: ignore
        
    def _subdivision_ray(self) -> ToricLatticeElement:
        '''
        returns the standard dividing ray of the cone depending on its type
        '''
        match self.type():
            case 'NE':
                return self.S.N(-self.S.K)
            case 'C':
                return self.S.N(sum(self.parent_face.rays()))
            case _:
                return self.S.N(sum(self.rays()))


    def children(self, subdivision_ray: ToricLatticeElement | None = None)->Iterable['NE_SubdivisionCone']:
        '''
        returns a generator of subdivision cones
        '''
        if subdivision_ray == None:
            subdivision_ray = self._subdivision_ray()
        for f in self.subdivision_faces(subdivision_ray):
            cone = NE_SubdivisionCone.from_face_and_ray(self, f, subdivision_ray)
            if not relint_contains_relint(self.cone, cone.cone):
                continue
            yield cone


    def ample_children(self, subdivision_ray: ToricLatticeElement | None = None)->Iterable['NE_SubdivisionCone']:
        '''
        returns a generator of subdivision cones whose relative interiors contain ample divisors
        
        EXAMPLES ::
        sage: cone_C = next(c for c in Surface(5).NE.ample_children() if c.type() == 'C')
        sage: sorted(Counter(c.type() for c in cone_C.ample_children()).items())
        [('C(0)', 1), ('C(1)', 6), ('C(2)', 12), ('C(3)', 4), ('C(3)-P1xP1', 4)]
        '''
        if subdivision_ray == None:
            subdivision_ray = self._subdivision_ray()
        ray_is_ample = self.S.Ample.relative_interior_contains(subdivision_ray)
        for cone in self.children(subdivision_ray):
            if ray_is_ample or cone.has_ample_divisors():
                yield cone
            


    def make_child(self, face:ConvexRationalPolyhedralCone, subdivision_ray: ToricLatticeElement | None = None)->'NE_SubdivisionCone':
        '''
        returns a subdivision cone corresponding to the given face
        '''
        # TODO convert ValueErrors into return None
        if subdivision_ray == None:
            subdivision_ray = self._subdivision_ray()
        if not self.cone.contains(subdivision_ray):
            raise ValueError(f'make_child: subdivision_ray {subdivision_ray} is not contained in this cone ({self} with rays {list(self.rays())}) of type {self.type()}')
        if not face.is_face_of(self.cone):
            raise ValueError(f'make_child: face (rays {list(face.rays())}) is not a face of this cone ({self} with rays {list(self.rays())}) of type {self.type()}')
        cone = NE_SubdivisionCone.from_face_and_ray(self, face, subdivision_ray)
        if not relint_contains_relint(self.cone, cone.cone):
            raise ValueError(f'make_child: resulted cone (rays {list(cone.cone.rays())}, type {cone.type()}) does not intersect the relative interior of this cone ({self} with rays {list(self.rays())}) of type {self.type()}')
        return cone
        # should we check for containing ample divisors? maybe not 

    def print(self):
        info = f'Cone of type {self.type()}, rays\n{self.rays()}, on {self.S}'
        if self.parent != None:
            info +=f' with parent of type {self.parent.type()}, parent ray {self.parent_ray}, parent face rays {list(self.parent.rays())}.'
        return info
        
    



    @cache
    def Ample(self):
        '''
        returns a cone, which relative interior consists of all ample classes in self.cone
        '''
        #TODO we assume that L is in NE, make this explicit
        ample = self.cone.intersection(self.S.Ample)
        if self.S.Ample.relative_interior_contains(sum(ample.rays())):
            return ample
        else:
            return Cone([],lattice=self.S.N)

    @property 
    def Ample2(self): # is this faster than Ample?
        dual_rays = self.S.NE.rays() + self.S.dual_cone(self.cone).rays()
        return self.S.dual_cone(Cone(dual_rays))

    def has_ample_divisors(self):
        return self.Ample().dimension() > 0
        
    @cache
    def type(self):
        '''
        Returns the Fujita type of the parent face for children of NE.
        EXAMPLES::
            sage: from collections import Counter
            sage: Counter(c.type() for c in Surface(4).NE.ample_children()).most_common()
            [('B(3)', 160),
            ('B(2)', 80),
            ('B(4)', 80),
            ('B(4)-P1xP1', 40),
            ('B(1)', 16),
            ('B(5)', 16),
            ('C', 10),
            ('B(0)', 1)]
        '''
        rank = self.cone.dim() - 1 
        if self == self.S.NE:
            return 'NE'
        elif self.parent == self.S.NE and self.parent_ray == -self.S.K:
            rays = list(self.parent_face.rays())
            if not all(r in self.S.minus_one_curves for r in rays):
                return 'NE.unknown-child-1'
            E = next(self.S.disjoint_subsets(rays))
            if len(E) == len(rays):
                res = f'B({rank})'
                other_disjoint_curves = self.S.curves_not_meeting(self.S.minus_one_curves, rays)
                if rank == 9 - self.S.degree - 1 and len(other_disjoint_curves)==0:
                    res+='-P1xP1'
                return res
            # below is not a complete check for type C. Do we need one? yes!
            meeting_curves = [[r for  r in rays if self.S.dot(r,e)==1 ] for e in E]
            if not all(len(curves)==1  for curves in meeting_curves):
                return 'NE.unknown-child-2'
            E1 = [curves[0] for curves in meeting_curves]
            B = E[0]+E1[0]
            if all(E[i]+E1[i]==B for i in range(len(E))) and \
                all(self.S.dot(e1,e2)<=0 for e1 in E1 for e2 in E1) and len(E)==rank-1:
                return 'C'
            return 'NE.unknown-child-3'
        elif self.parent.type() == 'C' and self.parent_ray == self.parent._subdivision_ray():
            rays = list(self.parent_face.rays())
            B = self.parent_ray
            E = [r for r in rays if r in self.S.minus_one_curves]
            has_anticanonical_ray = -self.S.K in rays
            if len(rays) - len(E) != 1 if has_anticanonical_ray else 0:
                #print(rays, E, B, rank)
                return 'C.unknown-child-6'
            if not all(self.S.dot(e1,e2)<=0 for e1 in E for e2 in E):
                return 'C.unknown-child-4'
            if not all(self.S.dot(B,e)==0 for e in E):
                return 'C.unknown-child-5'
            cone_type = f'C({len(E)})'
            if len(E) == len(self.S.E) - 1:
                if all(any(self.S.dot(c,e)!=0 for e in E) for c in self.S.minus_one_curves):
                    cone_type += '-P1xP1'
            if not has_anticanonical_ray:
                cone_type += '-no-K'
            return cone_type
        return self.parent.type() + '.unknown-child-0'

    #this method works slowly in degree 1, why?
    @classmethod 
    @cache 
    def representative(cls, S:Surface, cone_type:str):
        parent = S.NE
        match list(cone_type):
            case ['N','E']:
                return S.NE
            case ('B','(', num_rays, ')'):
                num_rays = int(num_rays)
                assert num_rays == int(re.search(r'\d+', cone_type).group()) # type: ignore
                face_rays = S.E[:num_rays]
            case ['C']:
                face_rays = S.E[:-1 ] + [S.L - e - S.E[-1 ] for e in S.E[:-1 ]]
            case ('C','(', num_rays, ')'):
                num_rays = int(num_rays)
                assert num_rays < 9 - S.degree
                face_rays = S.E[:num_rays] + [-S.K]
                parent = NE_SubdivisionCone.representative(S, 'C')
            case ('C','(', num_rays, ')', '-','n','o','-','K'):
                num_rays = int(num_rays)
                assert num_rays < 9 - S.degree
                face_rays = S.E[:num_rays]
                parent = NE_SubdivisionCone.representative(S, 'C')
            case _:
                num_rays = len(S.E) - 1
                if cone_type == f'B({num_rays})-P1xP1':
                    face_rays = S.E[:-2]+[S.L - S.E[-1] - S.E[-2]]
                elif cone_type == f'C({num_rays})-P1xP1':
                    face_rays = S.E[:-2] + [S.L - S.E[-1] - S.E[-2]] + [-S.K]
                    parent = NE_SubdivisionCone.representative(S, 'C')
                elif cone_type == f'C({num_rays})-P1xP1-no-K':
                    face_rays = S.E[:-2] + [S.L - S.E[-1] - S.E[-2]]
                    parent = NE_SubdivisionCone.representative(S, 'C')
                else:
                    raise ValueError('unknown cone type', cone_type)
        face_rays = sorted(normalize_rays(face_rays, S.N))
        face = Cone(face_rays, lattice=S.N)
        return parent.make_child(face)

    @staticmethod
    def cone_types(S:Surface):
        blowups = 9 - S.degree
        return ['NE', f'B({blowups-1 })-P1xP1', f'C({blowups-1 })-P1xP1', 'C']+            [f'B({i})' for i in range(blowups+1 )] + [f'C({i})' for i in range(blowups)]
        #removed:  [f'C({blowups-1 })-P1xP1-no-K']+ [f'C({i})-no-K' for i in range(blowups)]

    @classmethod
    def representatives(cls,S:Surface):
        for cone_type in cls.cone_types(S):
            yield cls.representative(S, cone_type)

    def relative_volume(self, cone:ConvexRationalPolyhedralCone):
        '''
        given a subcone of self, computes the intersection with an affine hyperplane orthogonal to -K and returns the volume of the subcone divided by the volume of self
        '''
        # see https://doc.sagemath.org/html/en/reference/discrete_geometry/sage/geometry/polyhedron/base7.html#sage.geometry.polyhedron.base7.Polyhedron_base7.volume
        raise NotImplementedError

