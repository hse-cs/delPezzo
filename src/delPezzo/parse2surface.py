from dataclasses import dataclass, field
import re
from typing import Generator
from delPezzo import Surface
from importlib import resources
import itertools



@dataclass
class WeakDependencies:
    '''
    This class represents dependencies of blowup points for a weak del Pezzo surface obtained from P^2, see [Pe23]_ for details. The numeration of points starts from 0.            

    INPUT: 
            - ``collinear_triples`` -- indices of triples of collinear blown up points.
            - ``infinitesimal_chains`` -- indices of chains of infinitely near blown up points. The next point in the chain is blown up infinitely near to the previous one. 
            - ``sixs_on_conic`` -- six-tuples of indices for six points on a conic if present.
            - ``cusp_cubics`` -- list of indices i for each cuspidal cubic 3*L-E_0-...-E_7-E_i in degree 1 
    
    '''
    collinear_triples: list[list[int]] = field(default_factory=list)
    infinitesimal_chains: list[list[int]] = field(default_factory=list)
    sixs_on_conic: list[list[int]] = field(default_factory=list)
    cusp_cubics: list[int] = field(default_factory=list)

    def is_trivial(self):
        '''
        return False if surface is not weak
        '''
        return len(self.collinear_triples)+len(self.infinitesimal_chains)+len(self.sixs_on_conic)+len(self.cusp_cubics)==0
    
    def degree_estimate(self):
        '''
        return maximal possible degree of the corresponding weak surface based on indices of mentioned points 
        '''
        list_to_flatten = self.collinear_triples + self.infinitesimal_chains + self.sixs_on_conic
        N_points = max([max(chain, default=-1) for chain in list_to_flatten], default=-1)+1 # 0 points for empty lists
        if len(self.cusp_cubics) > 0:
            N_points = max(N_points, 8)
        return 9 - N_points


    def is_valid(self):
        if self.degree_estimate() < 1:
            return False
        triples, chains, conics = self.collinear_triples, self.infinitesimal_chains, self.sixs_on_conic
        degree = self.degree_estimate()

        if degree <1:
            return False

        for triple in triples:
            if  len(triple) != 3 or len(set(triple)) != 3:
                return False

        # two lines intersect only by one point
        for triple1, triple2 in itertools.combinations(triples, 2):
            if len(set(triple1).intersection(set(triple2)))>1:
                return False

        # chains do not have duplicate entries
        if len(set(i for chain in chains for i in chain)) != sum(len(chain) for chain in chains):
            return False
        
        # line can contain only a prefix sublist of a chain
        for triple in triples:
            for chain in chains:
                if not self._point_line_and_chain_meet_correctly(triple, chain):
                    return False
        
        for six in conics:
            for triple in triples:
                if all(p in six for p in triple):
                    return False

        for six1, six2 in itertools.combinations(conics, 2):
            if len([p in six1 for p in six2]) >= 5:
                return False
        
        if degree<=2:
            raise NotImplementedError
        
        return True

    @classmethod
    def _point_line_and_chain_meet_correctly(cls, triple, chain):
        intersection = [i for i in chain if i in triple]
        return all(intersection[i] == chain[i] for i in range(len(intersection)))

#TODO test that all blowups of P2 give exactly Lubbes' list except P1xP1
    
    # def get_PicMarked(self):
    #     assert self.dependencies.is_valid()
    # def minus_two_curves(self) -> list['Curve']:
    #     collinear = [self.L - self.E[i] - self.E[j] - self.E[k] for i,j,k in self.dependencies.collinear_triples]
        
    #     infinitesimal = [self.E[chain[i]]-self.E[chain[i+1]] for chain in self.dependencies.infinitesimal_chains for i in range(len(chain)-1)]
        
    #     conic = [2*self.L - sum(self.E[i] for i in six) for six in self.dependencies.sixs_on_conic]
    #     cubic = [3*self.L - sum(self.E) - self.E[i] for i in self.dependencies.cusp_cubics]
    #     curves = collinear + infinitesimal + conic + cubic
    #     curves = normalize_rays(curves, self.N)
    #     return curves


    def __repr__(self):
        text = ""
        if self.collinear_triples:
            text += f",\n collinear_triples: {self.collinear_triples}"
        if self.infinitesimal_chains:
            text += f", infinitesimal_chains: {self.infinitesimal_chains}"
        if self.cusp_cubics:
            text += f", cusp_cubics: {self.cusp_cubics}"
        return text



def generate_surface(line: str) -> Surface:
    index, rank, line = line.strip().split(' ',2)
    list_contents, root_type = line.split(']',1)
    basis_labels = re.findall(r'\d+', list_contents)
    collinear_triples = [[int(i)-1 for i in b[1:]] for b in basis_labels if 
                        len(b)==4 and b[0]=='1']
    
    infinitesimal_chains = []
    for i,j in [b for b in basis_labels if len(b)==2]:
        i,j = int(i)-1, int(j)-1
        if len(infinitesimal_chains) == 0:
            infinitesimal_chains.append([i,j])
        else:
            if infinitesimal_chains[-1][-1] == i:
                infinitesimal_chains[-1].append(j)
            else:
                infinitesimal_chains.append([i,j])
    
    sixs_on_conic = [[i for i in range(8) if i+1 not in (int(b[1]),int(b[2]))] for b in basis_labels if len(b)==3 and b[0]=='2']
    cusp_cubics = [int(b[2])+1 for b in basis_labels if len(b)==3 and b[:2]=='30']
    extra = {'Lubbes_type':root_type, 'Lubbes_basis':basis_labels, 'Lubbes_index':index}
    dependencies = WeakDependencies(collinear_triples=collinear_triples, infinitesimal_chains=infinitesimal_chains, sixs_on_conic=sixs_on_conic, cusp_cubics=cusp_cubics)
    return Surface(9-int(rank), dependencies=dependencies, extra=extra)

def Lubbes_lines() -> list[str]:
    with resources.files("delPezzo").joinpath("Lubbes_list.txt").open() as file: 
        lines = file.readlines()
    return lines

def generate_surfaces(degree:int) -> Generator[Surface, None, None]:
    results = []
    pattern_list = r"\[\d+(?:[ \t]*,[ \t]*\d+)+\]"
    for line in Lubbes_lines():
        _, rank, _ = line.strip().split(' ',2)
        if rank != str(9-degree):
            continue
        yield generate_surface(line)
                

if __name__ == "__main__":
    for surface in generate_surfaces(5):
        print(surface)