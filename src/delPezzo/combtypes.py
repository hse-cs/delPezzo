from dataclasses import dataclass, field
import itertools
from typing import Generator
import networkx as nx
from collections import defaultdict
#from sage.all import *    #type: ignore
# uncomment the above line for type checking in VSCode, or comment it for doctesting with `sage -python -m doctest combtypes.py`

from delPezzo.cylinder import FibrationCylinder, FibrationCylinderImage, PreCylinder, CylinderList
from sage.matrix.constructor import Matrix
from sage.graphs.graph import Graph
from sage.graphs.digraph import DiGraph
from delPezzo.surface import Isomorphism, Point, Curve, Surface, SurfaceLabel
from delPezzo.surface2 import Surface2
from delPezzo.contraction import Contraction, ContractionToPlane
from delPezzo.picard import PicMap
#from delPezzo.cylinder import Cylinder, CylinderList

@dataclass
class CombType:
    '''
    a collection of isomorphic surfaces with a distinguished representative `S` and isomorphisms from it to other elements of the collection. 
    
    An additional field `maps` allows to store maps from `S` to representatives of other CombType objects
    '''
    S: Surface2
    other_surfaces_number: int = 0 #TODO remove?

    standard_single_contraction: Contraction | None = None
    standard_contraction_P2: ContractionToPlane | None = None

    #TODO compute these lists in CombTypes.Mor
    # single_contractions: list[tuple[Contraction, 'CombType']] = field(default_factory=list)
    # P2_contractions: list[ContractionToPlane] = field(default_factory=list)
    # blowups: list[Contraction] = field(default_factory=list)
    cylinders : CylinderList = field(init=False)

    degree: int = field(init=False)
    label: SurfaceLabel = field(init=False)


    def __post_init__(self):
        self.degree = self.S.degree
        self.label = self.S.label
        self.cylinders = CylinderList(cylinders=[], S=self.S)

    def __repr__(self)->str:
        return f"CombType(\nS={self.S},\nother={self.other_surfaces_number},single_con={self.standard_single_contraction},P2_con={self.standard_contraction_P2},cyl={len(self.cylinders)})"

@dataclass
class CombTypes:
    '''
    Lists all combinatorial types of surfaces of a given (anticanonical) degree and keeps track of maps between them

    FIELDS:
        - `negativity` -- the restriction on the absolute value of self-intersection of allowed negative curves
        - `degree_bound` -- the lower bound on degree of computed surfaces
        - `types` -- combinatorial types of surfaces enumerated by their canonical graphs
        - `standard_contraction` -- the initial contraction between two surfaces (initial contractions commute and represent a tree of blowups)
        - `Mor` -- contractions (up to some equivalence) between a pair of different surfaces

    TESTS:
        >>> len(CombTypes(precompute_degree=6).comb_types_of_degree[6])
        6
    '''
    negativity : int = 2
    degree_bound : int = 8
    _computed_degree: int = 8
    types : dict[SurfaceLabel, CombType] = field(default_factory=dict)
    Mor: defaultdict[tuple[SurfaceLabel,SurfaceLabel], list[Contraction]] = field(default_factory=lambda: defaultdict(list))
    

    def __post_init__(self):
        if self.negativity < 1:
            raise ValueError("negativity must be at least 1")
        if self.negativity > 2:
            raise NotImplementedError("we cannot compute negative and zero curves for blowups")
        if self.degree_bound > 8:
            raise ValueError("we have to prepopulate Hirzebruch surfaces")
        for r in range(0, self.negativity+1):
            Hr = Surface2.Hirzebruch(r)
            #key = Hr.canonical_label
            self._add_surface_only(Hr)
            if r==1:
                self._add_contraction(Hr.single_contractions()[0])

        if self.degree_bound < 8:
            self.compute_degree(self.degree_bound)
        # TODO: standard contractions

    def _add_surface_only(self, S:Surface) -> bool:
        '''
        add surface `S` to either existing CombType or a new one (without any maps); return True if added to a new one

                TESTS:
            >>> CT = CombTypes(); CT.add(Surface(9)); len(CT.comb_types_of_degree[9])
            1
        '''
        S = Surface2.convert_surface(S)
        key = S.label
        if key in self.types.keys():
            self.types[key].other_surfaces_number+=1
            return False
        self.types[key] = CombType(S=S)
        return True


    def add_surface_with_contractions(self, S: Surface)->None:
        '''
        add surface `S` with all its contractions
        '''
        S = Surface2.convert_surface(S)
        if self._add_surface_only(S):
            for C in S.single_contractions():
                self._add_contraction(C)

    def _add_contraction(self, contraction: Contraction)->None:
        '''
        add contraction and compute compositions with further contractions
        '''
        if contraction.dest.label not in self.types.keys():
            self.add_surface_with_contractions(contraction.dest)
        if contraction.src.label not in self.types.keys():
            raise ValueError(f"we assume that the source of the contraction is already present")

        correct_src = self.types[contraction.src.label].S
        correct_dest = self.types[contraction.dest.label].S

        isom_src = correct_src.isomorphism(contraction.src)
        isom_dest = contraction.dest.isomorphism(correct_dest)
        if isom_src == None:
            raise ValueError(f"surfaces {contraction.src} and {correct_src} have same canonical labe, but are not isomorphic")
        if isom_dest == None:
            raise ValueError(f"surfaces {contraction.dest} and {correct_dest} have same canonical labe, but are not isomorphic")
        correct_contraction = isom_dest * (contraction * isom_src)


        morphisms = self.Mor[(contraction.src.label, contraction.dest.label)]

        if any(correct_contraction.map==m.map for m in morphisms):
            return
        morphisms.append(contraction)


    def types_of_degree(self,degree:int):
        '''
        return combtypes of given degree
        '''
        return [ct for ct in self.types.values() if ct.degree == degree]

    def compute_degree(self, degree:int)->None:
        '''
        compute surfaces down to degree
        '''
        if self.degree_bound >= degree:
            self.degree_bound = degree
        if self._computed_degree <= degree:
            return

        self.compute_degree(degree+1)
        
        blowups_lists = [ct.S.blowups(self.negativity) for ct in self.types_of_degree(degree+1)]
        for blowup in [b for bl in blowups_lists for b in bl]:
            self.add_surface_with_contractions(blowup.src)
            self._add_contraction(blowup)


    #TODO construct from Lubbes' list here as a faster alternative?

    def populate_P2_contractions(self)->None:
        '''
        compute the list of contractions to P^2 for every combinatorial type if it is empty
        '''
        for combtype in self.descending_order():
            self._populate_P2_contractions_of_combtype(combtype)

    #TODO remove as deprecated
    # def populate_contractions(self, degree:int) -> None:
    #     '''
    #     compute contractions of combinatorial types of a given degree, both single (of one (-1)-curve) and to P^2

    #     TESTS:
    #         >>> C = CombTypes(precompute_degree=6); C.populate_contractions(7)
    #     '''
    #     if self.contractions_populated_to_degree <= degree:
    #         return
    #     if self.contractions_populated_to_degree > degree + 1:
    #         self.populate_contractions(degree+1)

    #     for combtype in self.comb_types_of_degree[degree]:
    #         self._populate_single_contractions_of_combtype(combtype)
    #         self._populate_P2_contractions_of_combtype(combtype)

    #     self.contractions_populated_to_degree = degree

    #     #TODO remove as unused
    # def  _populate_single_contractions_of_combtype(self, combtype: CombType)->None:
    #     '''
    #     populate contractions of a single (-1)-curve of `combtype`
        
    #     We assume that the upper comb.types are computed
        
    #     '''
    #     S = combtype.S
    #     degree = S.degree
    #     for e in S.minus_one_curves:
    #         C = Contraction.of_curves(S, [e])
    #         if C.dest.is_P1xP1():
    #             continue
    #         for upper_combtype in self.comb_types_of_degree[degree+1]:
    #             isom = C.dest.isomorphism(upper_combtype.S)
    #             if isom != None:
    #                 single_contraction = isom * C
    #                 combtype.single_contractions.append((single_contraction, upper_combtype))
    #                 break
    #         else:
    #             raise ValueError(f'no suitable destination comb type found for contraction {C}')


    def  _populate_P2_contractions_of_combtype(self, combtype)->None:
        '''
        compute contractions to P^2 of `combtype`
        
        We assume that single contractions of `combtype` are computed and contractions to P^2 of the upper combtypes are also computed
        '''
        if combtype.S.degree >= 8:
            combtype.P2_contractions = [c for c,_ in combtype.single_contractions]
            return
        for single_contraction, upper_combtype in combtype.single_contractions:
            for upper_P2_contraction in upper_combtype.P2_contractions:
                composition = upper_P2_contraction*single_contraction
                if all(composition.map!=other_contraction.map for other_contraction in combtype.P2_contractions):
                    combtype.P2_contractions.append(composition)
                    #print(len(combtype.P2_contractions))
        #TODO deduplicated ok?


    def __repr__(self) -> str:
        return f"CombTypes({self.types})"

    def descending_order(self) -> Generator[CombType, None, None]:
        '''
        yield all combtypes in self from max degree to min
        '''
        for label in sorted(self.types.keys(),reverse=True):
            yield self.types[label]



    def __len__(self) -> int:
        return len(self.types)

    def blowup_graph(self) -> DiGraph:
        '''
        return a directed graph of single contractions
        '''
        return DiGraph(
            data=[
                [ct.label for ct in self.descending_order()],
                [[u,v,len(self.Mor[(u,v)])] for u,v in self.Mor.keys()]
                ],
            format='vertices_and_edges',
            weighted=True,
            )


    def blowup_graph_pos(self):
        '''
        return positions for the blowup graph drawing
        '''
        counter = defaultdict(int)
        pos = dict()
        for combtype in self.descending_order():
            counter[combtype.degree] += 1
            pos[combtype.label] = (counter[combtype.degree],combtype.degree)
        return pos

    def blowup_graph_draw(self):
        '''
        draw the blowup graph with networkx
        '''
        import networkx as nx

        G = self.blowup_graph().networkx_graph()
        pos = self.blowup_graph_pos()

        def node_label(label):
            ctype = self.types[label]
            if ctype.S.is_weak_delPezzo:
                return ".".join(ctype.S.singularity_type())
            else:
                return str(label[2])
            
        labels = {p:node_label(p) for p in G.nodes}
        edge_labels = nx.get_edge_attributes(G, "weight")
        filtered_labels = {edge: w for edge, w in edge_labels.items() if w != 1}
        nx.draw(G,pos,  node_size=600, node_color="lightblue", font_size=7)
        nx.draw_networkx_labels(G,pos=pos,labels=labels)
        nx.draw_networkx_edge_labels(G,pos=pos,edge_labels=filtered_labels, font_color="red")

    #TODO  tree of standard contractions
        

    def morphisms_to(self, combtype:CombType)->list:
        '''
        return all contractions to combtype
        '''
        pairs = [(u,v) for u,v in self.Mor.keys() if v==combtype.label]
        return [m for p in pairs for m in self.Mor[p]]

    def morphisms_from(self, combtype:CombType)->list:
        '''
        return all contractions from combtype
        '''
        pairs = [(u,v) for u,v in self.Mor.keys() if u==combtype.label]
        return [m for p in pairs for m in self.Mor[p]]

    def cylinders(self, combtype:CombType, height:int=1)->CylinderList:
        '''
        compute the cylinders on `combtype` of at most provided height
        '''
        P2 = [ct for ct in self.types.values() if ct.degree == 9][0]
        if (combtype.label, P2.label) not in self.Mor.keys() and len(self.Mor[combtype.label,P2.label]) == 0:
            raise ValueError(f'no suitable morphism from {combtype} to P^2')
        cyls = CylinderList.from_zero_classes(self.Mor[combtype.label,P2.label][0])
        for contraction in self.morphisms_to(combtype): 
            for f in contraction.src.zero_classes:
                for e in contraction.C:
                    if e.dot(f)==1:
                        fibration = FibrationCylinder(contraction.src,f,e)
                        cyls.append(FibrationCylinderImage(contraction,fibration))
        return cyls

# TODO make poset-category by fixing standard contractions to P2 that commute with single ones.
# TODO PreCylinder abstract class with fibration and basepoint. Height.. Canonical representation of precylinder in poset-category as minimal fibration. Degree invariant?

if __name__ == "__main__":
    CT = CombTypes(degree_bound=5)
    CT.blowup_graph_draw()

    # for p in CT.descending_order():
    #     print(p)
    #     S = p.S
    #     print(S.neg_curves)

    #     if S.degree <=7:
    #         cyls = CylinderList.from_zero_classes(p.P2_contractions[0])
    #         print(cyls, "\ndim Forb=", cyls.Forb().dimension())
            
    #         for c in cyls:
    #             print("Cylinder: ", c.pic_class, c.basepoint_locus, c.section, c.curves_in_fibers)
    #             for ray in [-S.K, S.Ample._subdivision_ray()]:
    #                 print(ray, c.Pol.contains(ray), c.Pol.contains_relint(ray))
