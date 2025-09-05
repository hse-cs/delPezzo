class Surface:

    def Line(self,exceptional_curves:Sequence[ToricLatticeElement])-> ToricLatticeElement:
        triple_L = -self.K + sum(exceptional_curves)
        assert all(i%3==0 for i in triple_L), f"triple line from K={self.K} and E={exceptional_curves} not divisible by 3"
        return self.N([i/3  for i in triple_L])
        # we can divide by 3 if we provide all exceptional curves for contracting to P2


    def standard_contraction(self) -> 'Contraction':
        standard_contraction_lines = [e for e in self.minus_one_curves + self.minus_two_curves if self.dot(e, self.L) == 0]
        return Contraction(self, standard_contraction_lines)


    def contractions_P2(self) -> Generator['Contraction', None, None]:
        for minus_one_curves_to_contract in self.disjoint_subsets(self.minus_one_curves):
            for minus_two_curves_to_contract in itertools.combinations(self.minus_two_curves, 9-self.degree-len(minus_one_curves_to_contract)):
                contraction = Contraction.make_valid_contraction(self, minus_one_curves_to_contract+list(minus_two_curves_to_contract))
                if contraction != None:
                    #assert contraction.is_maximal()
                    yield contraction
            



class Contraction():
    '''
    S: A surface that is contracted
    contracted_curves: A tuple of contracted (irreducible) curves on S.
    E: a list of exceptional reducible (-1)-curves, which form an orthogonal basis of the span of the contracted curves. They are sums of chains of contracted (-2)-curves ending with a (-1)-curve.
    C: a list of contracted (irreducible) curves in the same order as E.
    '''
    S:Surface
    contracted_curves: tuple[ToricLatticeElement,...]
    E: tuple[ToricLatticeElement,...]
    C: tuple[ToricLatticeElement,...]

    def __init__(self, S:Surface, contracted_curves: Sequence[ToricLatticeElement]) -> None:
        """
        Initializes a new instance of the class.

        Args:
            S (Surface): The surface object.
            contracted_curves (Sequence[ToricLatticeElement]): A sequence of contracted curves.

        Returns:
            None
        """
        self.S = S
        self.contracted_curves = tuple(contracted_curves)
        E=[]
        C=[]
        assert self.is_valid(), f'contraction of curves {contracted_curves} is not valid'
        for chain in self.chains_of_contracted_curves:
            for i in range(len(chain)):
                C.append(chain[i])
                E.append(sum(chain[i:]))
        assert len(E) == len(C)
        self.E = tuple(E)
        self.C = tuple(C)

    @cached_property
    def chains_of_contracted_curves(self) -> list[list[ToricLatticeElement]]:
        '''
        returns list of lists of curves of form [C1,C2..,Cn], where Ei are irreducible contracted curves such that Cn^2=-1, Ci^2=-2 for i<n, and Ci*C_{i+1}=1.
        '''
        minus_one_curves = [c for c in self.contracted_curves if self.S.dot(c,c)==-1]
        minus_two_curves = [c for c in self.contracted_curves if self.S.dot(c,c)==-2]
        def find_chain(minus_one_curve:ToricLatticeElement)->list[ToricLatticeElement]:
            chain = [minus_one_curve]
            while True:
                next_curves = [c for c in minus_two_curves if self.S.dot(c,chain[-1])==1 and c not in chain]
                match len(next_curves):
                    case 0:
                        return list(reversed(chain))
                    case 1:
                        chain.append(next_curves[0])
                    case _:
                        raise ValueError("more than one next curve, should be a chain")
        return [find_chain(c) for c in minus_one_curves]
                
    def _E_to_C(self, e:ToricLatticeElement)->ToricLatticeElement:
        return self.C[self.E.index(e)]

    def _C_to_E(self, c:ToricLatticeElement)->ToricLatticeElement:
        assert c in self.C, f"{c} is not in {self.C}"
        assert len(self.E) == len(self.C), f"{self.E} and {self.C} have different lengths"
        return self.E[self.C.index(c)]

    @cached_property
    def L(self):
        '''
        returns the class of line on the contracted surface (we assume it to be P2)
        '''
        assert self.is_P2()
        return self.S.Line(self.E)


    def project(self, v):
        return v + sum(self.S.dot(e,v)*e for e in self.E)
        #return self.S.N(self.picard_projection_matrix*v)

    @classmethod
    def is_valid_contraction(cls, S:Surface, curves_to_contract: Sequence[ToricLatticeElement]) -> bool:
        g = S.gram_matrix(curves_to_contract)
        q = QuadraticForm(QQ, g)
        return q.is_negative_definite() and abs(g.det())==1

    @classmethod
    def make_valid_contraction(cls, S:Surface, curves_to_contract: Sequence[ToricLatticeElement]) -> Optional['Contraction']:
        if cls.is_valid_contraction(S, curves_to_contract):
            return cls(S, curves_to_contract)
        return None

    def is_valid(self) -> bool:
        return self.is_valid_contraction(self.S, self.contracted_curves)

    def is_maximal(self) -> bool:
        return all(self.dot(c,c)>=0 for c in 
                   self.S.minus_one_curves+self.S.minus_two_curves)        

    def is_P2(self) -> bool:
        return self.is_maximal() and len(self.contracted_curves) == 9-self.S.degree

    def dot(self, a, b):
        return self.S.dot(self.project(a),self.project(b))

    def gram_matrix(self, rays):
        return matrix([[self.dot(a,b) for a in rays] for b in rays])

    def __repr__(self) -> str:
        return f"contraction of curves {self.contracted_curves} on {self.S}"

    def are_collinear(self, c1, c2, c3) -> bool:
        E = [self._C_to_E(c) for c in (c1,c2,c3)]
        return self.L-sum(E) in self.S.minus_two_curves

    @cached_property
    def conic_classes(self) -> list[tuple[ToricLatticeElement,int]]:
        '''
        return a list of Picard classes of proper transforms of conics in P2, each with the dimension of the corresponding linear system.
        '''
        result = []
        for p in itertools.product(*[range(len(chain)+1) for chain in self.chains_of_contracted_curves]):
            dimension = 5 - sum(p)
            if dimension < 0:
                continue
            curves_on_conic = [curve for i,n in enumerate(p) for
                               curve in self.chains_of_contracted_curves[i][:n]]
            if any(self.are_collinear(c1,c2,c3) for c1,c2,c3 in itertools.combinations(curves_on_conic,3)):
                continue
            conic_class = 2*self.L - sum(self._C_to_E(c) for c in curves_on_conic)
            conic_class.set_immutable()
            result.append([conic_class, dimension])
        return result
    
    @cached_property
    def line_classes(self) -> list[tuple[ToricLatticeElement,int]]:
        '''
        return a list of Picard classes of proper transforms of lines in P2, each with the dimension of the corresponding linear system.
        UPD: actually, they are linear systems, i.e., smaller objects than classes
        '''
        #TODO rewrite by taking all collinear triples, then non-collinear pairs, then single base curves, and then a generic class
        result = []
        for p in itertools.product(*[range(len(chain)+1) for chain in self.chains_of_contracted_curves]):
            dimension = 2 - sum(p)
            if sum(p)>3:
                continue
            curves_on_line = [c for i,n in enumerate(p) for c in self.chains_of_contracted_curves[i][:n]]
            if any(self.are_collinear(c1,c2,c3)==False for c1,c2,c3 in itertools.combinations(curves_on_line,3)):
                continue
            dimension = 2 - len(curves_on_line)
            if dimension == -1:
                if self.are_collinear(*curves_on_line):
                    dimension = 0
                else:
                    continue
            
            # check that if two ci are on line, then another ci collinear with them is on line
            other_curves_meeting_line = [c for c in self.C if any(self.are_collinear(c1, c2, c) for c1, c2 in itertools.combinations(curves_on_line, 2))]            
            if not set(other_curves_meeting_line).issubset(set(curves_on_line)):
                continue
            
            line_class = self.L - sum(self._C_to_E(c) for c in curves_on_line)
            line_class.set_immutable()
            result.append([line_class, dimension])
        return result


