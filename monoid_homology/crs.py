"""
Monoid Homology Calculator
written by Dennis Sweeney

Given a monoid M, we can produce a topological space (cw complex) BM,
whose n-cells are n-tuples of non-identity elements of M.
This program computes the integral homology of the space BM.

The problem of deciding whether two words are equal is not computable,
so we restrict to nice classes of monoid presentations. In particular,
we look at "rewriting systems": an alphabet along with rules of the
form "L->R" (e.g. "xyz->xz"). These take the form a
finite collection of pairs of strings (L, R),
and we will write uLv --> uRv for any strings u and v.

A rewriting system is called "Complete" if is

    (1) Noetherian: No infinite chains w0 --> w1 --> w2 --> ...

    (2) Confluent: If a --> b and a --> c then
            there is some z with b --> z and c --> z

    (3) Normalized: If x->y is a rule then y is irreducible, and
            x is not reducible by any rule other than x->y.

Any word in such a system reduces to a unique irreducible form.
This gives rise to a monoid: irreducbile words with an operation
given by reducing their concatenation.

In [1], Ken Brown considers such systems and finds that the space BM
deformation retracts onto a smaller cell complex with only finitely
many cells in each dimension. The program below implements Brown's
collapsing scheme to find the finitely many "essential" cells
in each dimension, then computes the cellular homology of this
smaller complex, which will be equal to the homology of M.

This program requires SageMath to compute homology. To use:

    (1) Open a SageMath console or notebook.
    (2) Run the following command:
            load(URL OR PATH TO THIS FILE PERHAPS USING RAW BUTTON ON GITHUB)
    (3) Run the demo with demo(), or try your own:
            nat_nat = CRS('ab', [('ba', 'ab')])
            print(nat_nat.print_homology(10))

[1] Kenneth S. Brown. "The geometry of rewriting systems: A proof of the Anick-Groves-Squier theorem."
    In: Algorithms and classification in combinatorial group theory (Berkeley, CA, 1989), 137-163,
    Math. Sci. Res. Inst. Publ., 23, Springer, New York, 1992. MR1230632 (94g:20041), Zbl 0764.20016.
"""

from itertools import permutations
from collections import defaultdict, Counter, deque
from math import log, exp


# _cache_stats = {"essrep_hits": 0, "essrep_misses": 0,
#                 "classification_hits": 0, "classification_misses": 0,
#                 "essrep_hits": 0, "essrep_misses": 0,
#                 "reduce_hits": 0, "reduce_misses": 0,
#                 "successor_hits": 0, "successor_misses": 0}

# import os
# import psutil
# python_process = psutil.Process(os.getpid())
# def mem():
#     use = python_process.memory_info()[0] / (2.0**32)
#     return f"{use:.2f}GB"

class CompleteRewritingSystem:
    __slots__ = ("alphabet", "rules", "max_rewrites",
                 "prefix_to_rules", "essentials", "successor_words",
                 "_essrep", "_classifications", "_chain_complex",
                 "_essential_counts", "_reduction_cache")

    def __init__(self, alphabet, rules, max_rewrites=1000):
        self.alphabet = ''.join(alphabet)
        self.rules = rules
        self.max_rewrites = max_rewrites

        # Assert we're provided correct arguments
        if not isinstance(rules, list):
            raise ValueError("Rules must be a list of pairs of strings")
        for rule in rules:
            if not isinstance(rule, tuple) or len(rule) != 2:
                raise ValueError("Rules must be a list of pairs of strings")
        set_alphabet = set(alphabet)
        if len(set_alphabet) != len(alphabet):
            raise ValueError("duplicate letters in alphabet")
        letters = {c for rule in rules for side in rule for c in side}
        if not (letters <= set_alphabet):
            raise ValueError(f"{letters - set_alphabet} not in alphabet")

        # Assert normalized
        for _, right in rules:
            for left, _ in rules:
                if left in right:
                    raise ValueError(f"left side {left!r} "
                                     f"contains right side {right!r}")
        for (left1, _), (left2, _) in permutations(rules, 2):
            if left1 in left2:
                raise ValueError(f"left side {left2!r} "
                                 f"contains left side {left1!r}")
        # caches
        self._essrep = {}
        self._classifications = {}
        self._chain_complex = None
        self._essential_counts = ()
        self._reduction_cache = {}

        for a in alphabet:
            if self.reducible(a):
                raise ValueError(f"Single-letter {a!r} was reducible")

        # Collect proper nonempty prefixes/suffixes
        prefix_to_rules = defaultdict(list)
        suffix_to_rules = defaultdict(list)
        for rule in rules:
            left, _ = rule
            for i in range(1, len(left)):
                prefix, suffix = left[:i], left[i:]
                prefix_to_rules[prefix].append(rule)
                suffix_to_rules[suffix].append(rule)
        self.prefix_to_rules = dict(prefix_to_rules)

        # Tuples (a, b, c, reduce(a+b), reduce(b+c))
        criticals = []
        for middle in prefix_to_rules.keys() & suffix_to_rules.keys():
            right_rules = prefix_to_rules[middle]
            left_rules = suffix_to_rules[middle]
            for (left_before, left_after) in left_rules:
                for (right_before, right_after) in right_rules:
                    assert left_before[-len(middle):] == middle
                    subleft = left_before[:-len(middle)]
                    assert right_before[:len(middle)] == middle
                    subright = right_before[len(middle):]
                    criticals.append((subleft, middle, subright, left_after, right_after))

        # Assert convergent
        for (a, b, c, ab, bc) in criticals:
            ab_c = self._reduce(ab + c)
            a_bc = self._reduce(a + bc)
            if ab_c != a_bc:
                raise ValueError(f"Critical pair {(a,b,c)} did not resolve")

        self.essentials = {0: [()],
                           1: [(a,) for a in alphabet],
                           2: [(left[0], left[1:]) for left, right in rules]}

        # Breadth-first search for all words that appear in any essential tuple
        stack = deque({rest for (_, rest) in self.essentials[2]})
        successor_words = {}
        while stack:
            word = stack.pop()
            if word in successor_words:
                continue
            result = []
            for i in range(len(word)):
                suffix = word[i:]
                # XXX is there a faster/better way than this?
                for left, right in prefix_to_rules.get(suffix, ()):
                    assert left.startswith(suffix)
                    rest = left[len(suffix):]
                    if self.irreducible((word + rest)[:-1]):
                        result.append(rest)
            result = tuple(result)
            successor_words[word] = result
            stack.extend(result)
        self.successor_words = successor_words

    def __repr__(self):
        return f"CRS({self.alphabet!r}, {self.rules!r})"

    def __str__(self):
        rule_strings = [f"{left}->{right}" for left, right in self.rules]
        return f"Monoid( {self.alphabet} : {', '.join(rule_strings)} )"

    def reducible(self, word):
        return self.reduce(word) != word
        # any(left in word for left, right in self.rules)

    def irreducible(self, word):
        return self.reduce(word) == word
        # return all(left not in word for left, right in self.rules)

    def _reduce(self, word):
        word0 = word
        for _ in range(self.max_rewrites + 1):
            old = word
            for left, right in self.rules:
                word = word.replace(left, right)
            if word == old:
                return word
        raise RuntimeError(f"No fixed point was found for {word0}"
                           f"after {self.max_rewrites} iterations")

    def reduce(self, word):
        cache = self._reduction_cache
        if (res := cache.get(word)) is not None:
            # _cache_stats["reduce_hits"] += 1
            return res
        else:
            # _cache_stats["reduce_misses"] += 1
            res = self._reduce(word)
            cache[word] = res
            return res

    def op(self, word1, word2):
        return self.reduce(word1 + word2)

    def compute_essentials(self, up_to_dimension):
        for dim in range(2, up_to_dimension + 1):
            if dim in self.essentials:
                continue
            ess = []
            starts = self.essentials[dim-1]
            for start in starts:
                for word in self.successor_words[start[-1]]:
                    assert self.classify(start + (word,))[0] == "ESSENTIAL", (start, word)
                    ess.append(start + (word,))
            self.essentials[dim] = ess

        expected = self.essential_counts(up_to_dimension)
        actual = tuple([len(self.essentials[dim]) for dim in range(up_to_dimension + 1)])
        assert actual == expected, (actual, expected)

    def _essential_counts_by_dim_by_last(self, up_to_dimension):
        result = {0: Counter((None,)),
                  1: Counter(only for (only,) in self.essentials[1]),
                  2: Counter(last for (_, last) in self.essentials[2])}
        if up_to_dimension <= 2:
            return {k:v for k, v in result.items() if k <= up_to_dimension}
        # Using multiplication makes this faster than actually generating all of these.
        for dim in range(3, up_to_dimension + 1):
            new_by_last = Counter()
            for last, count in result[dim - 1].items():
                for word in self.successor_words[last]:
                    new_by_last[word] += count
            result[dim] = new_by_last
        return result         

    def essential_counts(self, up_to_dimension):
        if up_to_dimension + 1 <= len(self._essential_counts):
            return self._essential_counts[:up_to_dimension + 1]
        by_dim_by_last = self._essential_counts_by_dim_by_last(up_to_dimension)
        result = tuple([c.total() for c in by_dim_by_last.values()])
        self._essential_counts = result
        return result

    def complexity(self, iterations=5):
        """How fast does the number of cells grow? What is the base of the exponent?"""
        dim2 = Counter({last for _, last in self.essentials[2]})
        starting_total = dim2.total()
        if starting_total == 0:
            return 1.0
        # A sparse square zero-one matrix
        M = defaultdict(lambda: defaultdict(int))
        for word, succs in self.successor_words.items():
            for succ in succs:
                M[word][succ] += 1
        # Repeatedly square the (sparse) matrix
        for _ in range(iterations):
            square = defaultdict(lambda: defaultdict(int))
            for word, succ_counts in M.items():
                for succ, count1 in succ_counts.items():
                    if succ in M:
                        for succsucc, count2 in M[succ].items():
                            square[word][succsucc] += count1 * count2
            M = square
        # Matrix-vector product
        total = 0
        for word, count1 in dim2.items():
            for succsucc, count2 in M[word].items():
                total += count1 * count2
        if starting_total == 0:
            return 1.0
        if total == 0:
            return 0.0
        return exp((log(total) - log(starting_total)) / 2 ** iterations)

    def _classify_internal(self, cell):
        # TODO: make this recursive?
        # assert all(self.irreducible(w) for w in cell)
        if len(cell) == 0:
            return ("ESSENTIAL", None)
        if "" in cell:
            return ("DEGENERATE", None)
        if len(cell[0]) > 1:
            collapsible = (cell[0][0], cell[0][1:]) + cell[1:]
            return ("REDUNDANT", (collapsible, 1))
        for i in range(1, len(cell)):
            a, b = cell[i-1], cell[i]
            ab = a + b
            if self.irreducible(ab):
                redundant = cell[:i-1] + (ab,) + cell[i+1:]
                return ("COLLAPSIBLE", (redundant, i))
            if self.reducible(ab[:-1]):
                for j in range(1, len(b)):
                    b1, b2 = b[:j], b[j:]
                    if self.reducible(a + b1):
                        collapsible = cell[:i] + (b1, b2) + cell[i+1:]
                        return ("REDUNDANT", (collapsible, i+1))
                assert False
        return ("ESSENTIAL", None)

    def classify(self, cell):
        cache = self._classifications
        if cell in cache:
            # _cache_stats["classification_hits"] += 1
            return cache[cell]
        else:
            # _cache_stats["classification_misses"] += 1
            result = self._classify_internal(cell)
            cache[cell] = result
            return result

    def boundary(self, cell):
        assert self.classify(cell)[0] == "ESSENTIAL"
        if len(cell) <= 1:
            return
        yield from self.essential_representation(cell[1:], (-1)**0)
        for i in range(1, len(cell)):
            q = self.op(cell[i-1], cell[i])
            face = cell[:i-1] + (q,) + cell[i+1:]
            yield from self.essential_representation(face, (-1)**i)
        yield from self.essential_representation(cell[:-1], (-1)**len(cell))

    def _essential_representation_internal(self, cell, sign):
        # TODO: Make this recursive?
        kind = self.classify(cell)
        if kind[0] == "ESSENTIAL":
            return ((sign, cell),)
        elif kind[0] == "COLLAPSIBLE":
            return ()
        elif kind[0] == "DEGENERATE":
            return ()
        elif kind[0] == "REDUNDANT":
            collapsible, index = kind[1]
            assert len(collapsible) >= 1
            result = []
            for i in range(0, len(collapsible) + 1):
                subsign = sign * (-1)**i * ((-1)**index * -1)
                if i == index:
                    continue
                elif i == 0:
                    result.extend(self.essential_representation(collapsible[1:], subsign))
                elif i == len(collapsible):
                    result.extend(self.essential_representation(collapsible[:-1], subsign))
                else:
                    x = self.op(collapsible[i-1], collapsible[i])
                    face = collapsible[:i-1] + (x,) + collapsible[i+1:]
                    result.extend(self.essential_representation(face, subsign))
            return tuple(result)
        else:
            raise AssertionError

    def essential_representation(self, cell, sign=+1):
        cache = self._essrep
        if (cell, sign) in cache:
            # _cache_stats["essrep_hits"] += 1
            return cache[cell, sign]
        else:
            # _cache_stats["essrep_misses"] += 1
            result = self._essential_representation_internal(cell, sign)
            cache[cell, sign] = result
            return result
        # return self._essential_representation_internal(cell, sign)

    def chain_complex(self, up_to_dimension):
        if (_cc := self._chain_complex) is not None:
            if set(range(1, up_to_dimension + 1)) == set(_cc):
                return self._chain_complex
            if set(range(1, up_to_dimension + 1)) <= set(_cc):
                return {dim: _cc[dim] for dim in range(1, up_to_dimension + 1)}

        self.compute_essentials(up_to_dimension)
        cell_to_index = {}
        for dim, ess_list in self.essentials.items():
            for i, cell in enumerate(ess_list):
                cell_to_index[cell] = i
        matrices = {}
        for dim in range(1, up_to_dimension + 1):
            m = len(self.essentials[dim - 1])
            n = len(self.essentials[dim])
            M = [[0]*n for _ in range(m)]
            for cell in self.essentials[dim]:
                celli = cell_to_index[cell]
                for coeff, face in self.boundary(cell):
                    M[cell_to_index[face]][celli] += coeff
            matrices[dim] = M
        self._chain_complex = matrices
        return matrices

    def SAGE_chain_complex(self, up_to_dimension, check=True, verbose=False):
        # local imports so the rest can be run in vanilla Python without SAGE
        from sage.matrix.constructor import Matrix
        from sage.homology.chain_complex import ChainComplex
        from sage.rings.integer_ring import ZZ

        if verbose:
            print(f"Computing essentials...")
        self.compute_essentials(up_to_dimension)
        if verbose:
            print(f"Indexing...")
        cell_to_index = {}
        for dim, ess_list in self.essentials.items():
            for i, cell in enumerate(ess_list):
                cell_to_index[cell] = i
        matrices = {}
        for dim in range(1, up_to_dimension + 1):
            if verbose:
                print(f"Working on dimension {dim}...")
            m = len(self.essentials[dim - 1])
            n = len(self.essentials[dim])
            M = Matrix(ZZ, m, n, sparse=True)
            ess = self.essentials[dim]
            if verbose:
                print(f"Allocated matrix...")
                from tqdm import tqdm
                ess = tqdm(ess, smoothing=0.0001, dynamic_ncols=True)
            for cell in ess:
                celli = cell_to_index[cell]
                for coeff, face in self.boundary(cell):
                    M[cell_to_index[face], celli] += coeff
            matrices[dim] = M
        return ChainComplex(matrices, degree_of_differential=-1, check=check)

    def sympy_rational_homology_ranks(self, up_to_dimension):
        # SAGE is more efficient because it delegates to PARI,
        # but we can at least get the ranks without anything fancy.

        # local imports so the rest can be run in vanilla Python without sympy
        from sympy.matrices import Matrix

        matrices = self.chain_complex(up_to_dimension + 1)
        boundary_ranks = {dim: Matrix(matrices[dim]).rank()
                          for dim in range(1, up_to_dimension + 2)}
        return [
            (len(self.essentials[dim])
                - boundary_ranks.get(dim, 0) # only count cycles
                - boundary_ranks.get(dim + 1, 0) # kill off boundaries
                )
            for dim in range(up_to_dimension + 1)]

    def homology(self, up_to_dimension,
                 base_ring=None,
                 generators=False,
                 verbose=False,
                 algorithm='auto',
                 check=False):
        cc = self.SAGE_chain_complex(up_to_dimension + 1, check=check, verbose=verbose)
        return {dim: cc.homology(deg=dim,
                                 base_ring=base_ring,
                                 generators=generators,
                                 verbose=verbose,
                                 algorithm=algorithm)
                for dim in range(0, up_to_dimension + 1)}

    def homology_list(self, up_to_dimension, **kwargs):
        h = self.homology(up_to_dimension, **kwargs)
        return [h[i] for i in range(1, up_to_dimension + 1)]

    def print_homology(self, up_to_dimension, **kwargs):
        print(self)
        self.compute_essentials(up_to_dimension + 1)
        print("essential cell counts:", [len(ess_list) for ess_list in self.essentials.values()])
        cc = self.SAGE_chain_complex(up_to_dimension + 1, check=False)
        print(f"Made SAGE chain complex.")
        for dim in range(up_to_dimension + 1):
            H_i = cc.homology(dim, **kwargs)
            print(f"H_{dim} = {H_i}")
        print()

CRS = CompleteRewritingSystem
