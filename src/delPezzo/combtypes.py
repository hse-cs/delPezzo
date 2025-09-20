from dataclasses import dataclass, field
import itertools
from typing import Generator
import networkx as nx
#from sage.all import *    #type: ignore
# uncomment the above line for type checking in VSCode, or comment it for doctesting with `sage -python -m doctest combtypes.py`

from delPezzo.cylinder import Cylinder
from sage.matrix.constructor import Matrix

from delPezzo.surface import Isomorphism, Point, Curve, Surface
from delPezzo.surface2 import Surface2
from delPezzo.contraction import Contraction, ContractionToPlane
from delPezzo.picard import PicMap

@dataclass
class CombType:
    '''
    a collection of isomorphic surfaces with a distinguished representative and isomorphisms from it to other elements of the collection. 
    
    An additional field `maps` allows to store maps from `representative` to representatives of other CombType objects
    '''
    representative: Surface2
    other_surfaces_number: int = 0
    single_contractions: list[tuple[Contraction, 'CombType']] = field(default_factory=list)
    P2_contractions: list[ContractionToPlane] = field(default_factory=list)
    blowups: list[Contraction] = field(default_factory=list)
    cylinders : list[Cylinder] = field(default_factory=list)

    def __repr__(self)->str:
        return f"CombType(\nrepresentative={self.representative},\nother={self.other_surfaces_number},single_con={len(self.single_contractions)},P2_con={len(self.P2_contractions)},blowups={len(self.blowups)},cyl={len(self.cylinders)})"


class CombTypes:
    '''
    Lists all combinatorial types of surfaces of a given (anticanonical) degree and keeps track of maps between them

    FIELDS:
        - `comb_types_of_degree` -- a dict of computed surfaces (up to isomorphism) for each degree
        - `contractions_populated_to_degree` -- contractions are computed up to this degree

    TESTS:
        >>> len(CombTypes(precompute_degree=6).comb_types_of_degree[6])
        6
    '''

    def __init__(self, negativity: int=2, precompute_degree:int=8):
        '''
        INPUT:
            - `negativity` -- the minimal allowed self-intersection of negative curves
        '''
        if negativity < 1:
            raise ValueError("negativity must be at least 1")
        if negativity > 2:
            raise NotImplementedError("we cannot compute negative and zero curves for blowups")
        self.negativity = negativity
        P2_type = CombType(representative=Surface2(9))
        Hirzebruch_types = [CombType(representative=Surface2.Hirzebruch(r)) for r in range(0, self.negativity+1)]
        self.comb_types_of_degree : dict[int,list[CombType]] = {9:[P2_type], 8: Hirzebruch_types}

        F1_type = Hirzebruch_types[1]
        F1 = Hirzebruch_types[1].representative
        P2 = P2_type.representative
        E = F1.neg_curves[0]
        pullback_map = PicMap[Surface](src=P2, dest=F1, map=Matrix([[1], [0]]))
        F1_P2_map = ContractionToPlane(src=F1, dest=P2, map=Matrix([[1,0]]), C=[E], E=[E], pullback_map=pullback_map)
        F1_type.single_contractions.append((F1_P2_map, P2_type))
        F1_type.P2_contractions.append(F1_P2_map)

        self.contractions_populated_to_degree = 8
        if precompute_degree<8:
            self.compute_degree(precompute_degree)


    def add(self, S: Surface, contraction: Contraction|None=None, upper:CombType|None=None)->None:
        '''
        add surface `S` to either existing CombType or a new one
        
        if contraction and upper combtype are present, we add it to the list of single contractions of self and of blowups of upper

        TESTS:
            >>> CT = CombTypes(); CT.add(Surface(9)); len(CT.comb_types_of_degree[9])
            1
        '''
        S=Surface2.convert_surface(S)
        
        if S.degree not in self.comb_types_of_degree.keys():
            self.comb_types_of_degree[S.degree] = []
        
        candidate_ctypes = [ct for ct in self.comb_types_of_degree[S.degree] if ct.representative.singularity_type() == S.singularity_type()]
        isom = None
        for ct in candidate_ctypes:
            isom = ct.representative.isomorphism(S)
            if isom != None:
                ct.other_surfaces_number+=1
                combtype = ct
                break
        else:            
            combtype = CombType(representative=S)
            self.comb_types_of_degree[S.degree].append(combtype)

        if contraction != None and upper != None:
            if isom != None:
                contraction = contraction * isom #type: ignore
            combtype.single_contractions.append((contraction, upper)) #type: ignore
            upper.blowups.append(contraction) #type: ignore
        


    def compute_degree(self, degree:int)->None:
        '''
        compute (weak) del Pezzo surfaces of given degree
        '''
        if degree in self.comb_types_of_degree.keys():
            return
        self.compute_degree(degree+1)
        
        for combtype in self.comb_types_of_degree[degree+1]:
            for contraction in combtype.representative.blowups_nonequivalent_over_P2(self.negativity):
                self.add(contraction.src, contraction, combtype)


    #TODO construct from Lubbes' list here as a faster alternative?

    def populate_P2_contractions(self)->None:
        '''
        compute the list of contractions to P^2 for every combinatorial type if it is empty
        '''
        for degree in self.comb_types_of_degree.keys():
            for combtype in self.comb_types_of_degree[degree]:
                if combtype.P2_contractions == []:
                    self._populate_P2_contractions_of_combtype(combtype)

    #TODO remove as deprecated
    def populate_contractions(self, degree:int) -> None:
        '''
        compute contractions of combinatorial types of a given degree, both single (of one (-1)-curve) and to P^2

        TESTS:
            >>> C = CombTypes(precompute_degree=6); C.populate_contractions(7)
        '''
        if self.contractions_populated_to_degree <= degree:
            return
        if self.contractions_populated_to_degree > degree + 1:
            self.populate_contractions(degree+1)

        for combtype in self.comb_types_of_degree[degree]:
            self._populate_single_contractions_of_combtype(combtype)
            self._populate_P2_contractions_of_combtype(combtype)

        self.contractions_populated_to_degree = degree

        #TODO remove as unused
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


    def __getitem__(self, degree:int)->list[CombType]:
        return self.comb_types_of_degree[degree]

    def __repr__(self) -> str:
        return f"CombTypes{self.comb_types_of_degree.__repr__()}"

    def descending_order(self) -> Generator[CombType, None, None]:
        '''
        yield all combtypes in self from top degree to bottom
        '''
        for degree in sorted(self.comb_types_of_degree.keys(),reverse=False):
            for combtype in self[degree]:
                yield combtype

    def graph(self):
        G = nx.MultiDiGraph()
        pos = dict()
        for combtype in self.descending_order():
            G.add_node(combtype.representative)
            for _, upper_combtype in combtype.single_contractions:
                G.add_edge(combtype.representative, upper_combtype.representative)
        for d in self.comb_types_of_degree.keys():
            for i,combtype in enumerate(self.comb_types_of_degree[d]):
                pos[combtype.representative] = (i,d)
        return G, pos
        

if __name__ == "__main__":
    CT = CombTypes(precompute_degree=5)
    #CT.populate_P2_contractions()
    G,pos = CT.graph()
    def edge_label(u,v):
        m = G.number_of_edges(u,v)
        return m if m>1 else ""
    edge_labels = {(u,v,):edge_label(u,v)
             for u,v in G.edges()}
    nx.draw_networkx_edge_labels(G,pos,edge_labels=edge_labels)
    nx.draw(G,pos, labels={p:'.'.join(p.singularity_type()) for p in G.nodes})