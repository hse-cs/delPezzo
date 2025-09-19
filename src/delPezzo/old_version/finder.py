#from sage.all_cmdline import *   # import sage library, otherwise other imports break #type: ignore
from sage.geometry.cone import ConvexRationalPolyhedralCone

from dataclasses import dataclass

from .surface import Surface
from .cylinder import CylinderList
from .cone import NE_SubdivisionCone
from .cylinder import CylinderGenerator

@dataclass
class ConeCovering:
    NE_cone: NE_SubdivisionCone
    collection: CylinderList
    is_generically_flexible: bool

class Finder:
    """
    This class performs search of cylinder collections on a (weak) del Pezzo surface
    """
    def __init__(self, S:Surface, constructions: list[str]|None=None, recommended_coverings: list[CylinderList]|None=None) -> None:
        self.S = S
        self.constructions = constructions or ['LL']
        self.recommended_coverings : list[CylinderList] = recommended_coverings or []
        self.all_cylinders = CylinderList(list(CylinderGenerator.all_cylinders(S, self.constructions)), S)
        self.coverings = [self.find_covering_on_cone(self.S.NE)]

    def find_covering_on_cone(self, NE_cone: NE_SubdivisionCone) -> ConeCovering:
        cone = NE_cone.cone
        for collection in self.recommended_coverings:
            if collection.is_generically_flexible_on(cone):
                return ConeCovering(NE_cone, collection, True)
        collection = self.all_cylinders.copy()
        collection = collection.get_polar_on(cone).reduce()
        return ConeCovering(NE_cone, collection, collection.is_generically_flexible_on(cone, restrict_to_ample=True))

    def all_coverings_are_genflex(self) -> bool:
        '''
        return True if generic flexibility for all polarizations is achieved
        '''
        return len(self.coverings)>0 and all(covering.is_generically_flexible for covering in self.coverings)

    def iterate(self):
        '''
        subdivide cones of polarizations, where generic flexibility is not yet achieved; return True if generic flexibility for all polarizations is achieved
        '''
        bad_coverings = [covering  for covering in self.coverings if not covering.is_generically_flexible]
        for covering in bad_coverings:
            self.coverings.remove(covering)
            for new_cone in covering.NE_cone.children(): #NE or Cone?
                self.coverings.append(self.find_covering_on_cone(new_cone))
        return self.all_coverings_are_genflex()
    