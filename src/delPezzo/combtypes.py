from dataclasses import dataclass, field
from delPezzo.picard import PicMap
from sage.all import *    #type: ignore
# uncomment the above line for type checking in VSCode, or comment it for doctesting with `sage -python -m doctest combtypes.py`

from delPezzo.surface import Isomorphism, Point, Curve, Surface

@dataclass
class CombType:
    '''
    a collection of isomorphic surfaces with a distinguished representative and isomorphisms from it to other elements of the collection. 
    
    An additional field `maps` allows to store maps from `representative` to representatives of other CombType objects
    '''

    representative: Surface
    other_surfaces: list[Isomorphism] #TODO remove?
    maps: list[tuple[PicMap[Surface], 'CombType']] = field(default_factory=list)


class CombTypes:
    '''
    Lists all combinatorial types of surfaces of a given (anticanonical) degree and keeps track of maps between them

    FIELDS:
        - `comb_types_of_degree` -- a dict of computed surfaces (up to isomorphism) for each degree
        - `wdP_only` -- a dict of booleans for each degree whether we computed only (weak) del Pezzo surfaces 

    TESTS:
        >>> len(CombTypes(6).comb_types_of_degree[6])
        6
    '''

    def __init__(self, degree: int=8):
        '''
        INPUT:
            - `degree` -- the degree of weak del Pezzo surfaces (except P1xP1) that we compute for starters. Equals or less than 8.
        '''
        initial_comb_type = CombType(Surface(8), [])
        self.comb_types_of_degree : dict[int,list[CombType]] = {8:[initial_comb_type]}
        #self.min_computed_degree : int = 8
        self.switch_to_any_surface_at_degree : int = 0
        self.compute_wdP_in_degree(degree)

    def compute_wdP_in_degree(self, degree:int)->None:
        '''
        compute (weak) del Pezzo surfaces of given degree
        '''
        if degree in self.comb_types_of_degree.keys():
            return
        if degree <= self.switch_to_any_surface_at_degree:
            raise ValueError("We switched from wdP to arbitrary blowups at this degree")
        self.compute_wdP_in_degree(degree+1)
        
        upper_representatives = [combtype.representative for combtype in self.comb_types_of_degree[degree+1]]
        blowups = [blowup for S in upper_representatives for blowup in S.blowups_nonequivalent_over_P2(minus_one_only=True)]
        sing_types_of_blowups = set([blowup.dest.singularity_type() for blowup in blowups])
        blowups_by_type = {sing_type: [blowup for blowup in blowups if blowup.dest.singularity_type()==sing_type] for sing_type in sing_types_of_blowups}

        new_comb_types = []


        for blowups_subset in blowups_by_type.values():
            while len(blowups_subset)>0:
                new_representative = blowups_subset.pop().dest
                isomorphic_elements = []
                blowups_to_remove = []
                for b in blowups_subset:
                    isom = new_representative.isomorphism(b.dest)
                    if isom == None:
                        continue
                    isomorphic_elements.append(isom)
                    blowups_to_remove.append(b)
                for b in blowups_to_remove:             blowups_subset.remove(b)
                new_comb_types.append(CombType(new_representative, isomorphic_elements))

        self.comb_types_of_degree[degree] = new_comb_types

    #TODO construct from Lubbes' list here as a faster alternative. 

if __name__ == "__main__":
    CombTypes(6)