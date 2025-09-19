from dataclasses import dataclass, field
#from sage.all import *    #type: ignore
# uncomment the above line for type checking in VSCode, or comment it for doctesting with `sage -python -m doctest combtypes.py`

from sage.matrix.constructor import Matrix

from delPezzo.surface import Isomorphism, Point, Curve, Surface
from delPezzo.contraction import Contraction, ContractionToPlane
from delPezzo.picard import PicMap

@dataclass
class CombType:
    '''
    a collection of isomorphic surfaces with a distinguished representative and isomorphisms from it to other elements of the collection. 
    
    An additional field `maps` allows to store maps from `representative` to representatives of other CombType objects
    '''

    representative: Surface
    other_surfaces: list[Isomorphism] = field(default_factory=list) #TODO remove?
    single_contractions: list[tuple[PicMap[Surface], 'CombType']] = field(default_factory=list)
    P2_contractions: list[PicMap[Surface]] = field(default_factory=list)
    is_wdP: bool = field(init=False)

    def __post_init__(self):
        self.is_wdP = self.representative.is_weak_delPezzo

class CombTypes:
    '''
    Lists all combinatorial types of surfaces of a given (anticanonical) degree and keeps track of maps between them

    FIELDS:
        - `comb_types_of_degree` -- a dict of computed surfaces (up to isomorphism) for each degree
        - `contractions_populated_to_degree` -- contractions are computed up to this degree

    TESTS:
        >>> len(CombTypes(6).comb_types_of_degree[6])
        6
    '''

    def __init__(self, negativity: int=2):
        '''
        INPUT:
            - `negativity` -- the minimal allowed self-intersection of negative curves
        '''
        if negativity < 1:
            raise ValueError("negativity must be at least 1")
        if negativity > 2:
            raise NotImplementedError("we cannot compute negative and zero curves for blowups")
        self.negativity = negativity
        P2_type = CombType(representative=Surface(9))
        Hirzebruch_types = [CombType(representative=Surface.Hirzebruch(r)) for r in range(0, self.negativity)]
        self.comb_types_of_degree : dict[int,list[CombType]] = {9:[P2_type], 8: Hirzebruch_types}

        F1_type = Hirzebruch_types[1]
        F1 = Hirzebruch_types[1].representative
        P2 = P2_type.representative
        E = F1.neg_curves[0]
        pullback_map = PicMap[Surface](src=P2, dest=F1, map=Matrix([[1, 0]]))
        F1_P2_map = ContractionToPlane(src=F1, dest=P2, map=Matrix([[1],[0]]), C=[E], E=[E], pullback_map=pullback_map)
        F1_type.single_contractions.append((F1_P2_map, P2_type))
        F1_type.P2_contractions.append(F1_P2_map)

        self.contractions_populated_to_degree = 8

    def compute_surfaces_in_degree(self, degree:int)->None:
        '''
        compute (weak) del Pezzo surfaces of given degree
        '''
        if degree in self.comb_types_of_degree.keys():
            return
        self.compute_surfaces_in_degree(degree+1)
        
        upper_representatives = [combtype.representative for combtype in self.comb_types_of_degree[degree+1]]
        blowups = [blowup for S in upper_representatives for blowup in S.blowups_nonequivalent_over_P2(self.negativity)]
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


    def populate_contractions(self, degree:int) -> None:
        '''
        compute contractions of combinatorial types of a given degree, both single (of one (-1)-curve) and to P^2

        TESTS:
            >>> C = CombTypes(6); C.populate_contractions(7)
        '''
        if self.contractions_populated_to_degree <= degree:
            return
        if self.contractions_populated_to_degree > degree + 1:
            self.populate_contractions(degree+1)

        for combtype in self.comb_types_of_degree[degree]:
            self._populate_single_contractions_of_combtype(combtype)
            self._populate_P2_contractions_of_combtype(combtype)

        self.contractions_populated_to_degree = degree


    def  _populate_single_contractions_of_combtype(self, combtype: CombType)->None:
        '''
        populate contractions of a single (-1)-curve of `combtype`
        
        We assume that the upper comb.types are computed
        
        '''
        S = combtype.representative
        degree = S.degree
        for e in S.minus_one_curves:
            C = Contraction.of_curves(S, [e])
            if C.dest.is_P1xP1():
                continue
            for upper_combtype in self.comb_types_of_degree[degree+1]:
                isom = C.dest.isomorphism(upper_combtype.representative)
                if isom != None:
                    single_contraction = isom * C
                    combtype.single_contractions.append((single_contraction, upper_combtype))
                    break
            else:
                raise ValueError(f'no suitable destination comb type found for contraction {C}')


    def  _populate_P2_contractions_of_combtype(self, combtype)->None:
        '''
        compute contractions to P^2 of `combtype`
        
        We assume that single contraction of `combtype` are computed and contractions to P^2 of the upper comb.types are also computed
        '''
        if combtype.representative.degree == 8:
            combtype.P2_contractions = [c for c,_ in combtype.single_contractions]
            return
        for single_contraction, upper_combtype in combtype.single_contractions:
            for upper_P2_contraction in upper_combtype.P2_contractions:
                composition = upper_P2_contraction*single_contraction
                if all(composition.map!=other_contraction.map for other_contraction in combtype.P2_contractions):
                    combtype.P2_contractions.append(composition)


if __name__ == "__main__":
    CombTypes(6).populate_contractions(7)