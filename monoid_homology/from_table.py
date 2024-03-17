"""
Manipulating finite semigroups by their multiplication table.
"""

from itertools import chain, combinations
from functools import cache
from pathlib import Path
import string

from .knuth_bendix import normalize
from .crs import CRS

DATA_DIR = Path(__file__).parent.parent / "finite_semigroup_data"

SYMBOLS = string.ascii_uppercase + string.ascii_lowercase + string.digits


@cache
def all_op_strings(num_elts):
    with open(DATA_DIR / f"{int(num_elts)}elt_semis.txt", "r") as f:
        return f.readlines()

def string_to_op(s):
    return [list(map(int, row)) for row in s.rstrip().split(";")]

def op_from_index(num_elts, index):
    if index == 0:
        raise ValueError("GAP smallsemi package uses 1-based indexing")
    return string_to_op(all_op_strings(num_elts)[index - 1])


def representation_by_generators(op, gens):
    """Given an operation table and a set of generators,
    represent all monoid elements using the generators.
    """
    n = len(op)
    assert {x for row in op for x in row} <= set(range(n))
    assert set(gens) <= set(range(n))

    folded = {(g,): g for g in gens}
    representation = {g: (g,) for g in gens}
    if len(representation) == n:
        return representation

    while True:
        new_folded = {}
        for tup, res in folded.items():
            for g in gens:
                tupg = tup + (g,)
                resg = op[res][g]
                if resg not in representation:
                    new_folded[tupg] = resg
                    representation[resg] = tupg
                    if len(representation) == n:
                        return representation
        if not new_folded:
            # no progress made
            return None
        else:
            folded = new_folded


def relation_tuple_pairs(op, rep):
    """
    Given an operation and a representation of all elements by generators,
    list all relations in the semigroup in terms of the generators.    
    """
    elts = range(len(op))
    return [(rep[a] + rep[b], rep[op[a][b]]) for a in elts for b in elts]

def relation_str_pairs(op, rep, alphabet, gens):
    g2s = dict(zip(gens, alphabet, strict=True))
    tuple_pairs = relation_tuple_pairs(op, rep)
    def convert(tup):
        return "".join(map(g2s.get, tup))
    return [(convert(left), convert(right)) for left, right in tuple_pairs]

def all_gens_crs(op):
    """
    The CRS where the rewriting system is just all the generators
    subject to all the relations.
    """
    n = len(op)
    gens = range(n)
    rep = representation_by_generators(op, gens)
    alphabet = SYMBOLS[:n]
    pairs = relation_str_pairs(op, rep, alphabet, gens)
    return CRS(alphabet, pairs)

def nonempty_powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(1, len(s)+1))

def find_best_gens_crs(op, maxdim, verbose=False):
    """
    Brute search to find the set of generators
    that make for the smallest essential chain complex from the CRS.
    """
    n = len(op)
    
    cost_best_crs, best_crs = None, None
    for num_gens in range(1, n + 1):
        alphabet = SYMBOLS[:num_gens]
        for gens in combinations(range(n), num_gens):
            rep = representation_by_generators(op, gens)
            if rep is None:
                continue
            pairs = relation_str_pairs(op, rep, alphabet, gens)
            pairs = normalize(pairs) # this should terminate?
            crs = CRS(alphabet, pairs)
            lengths = crs.essential_counts(maxdim + 1)
            if verbose:
                print(gens, lengths)
            # total size of boundary matrices
            cost = sum(a*b for a, b in zip(lengths, lengths[1:]))
            if best_crs is None or cost < cost_best_crs:
                cost_best_crs, best_crs = cost, crs
    if verbose:
        print("Best:", best_crs.essential_counts(maxdim + 1))
    return best_crs

def best_gens_crs_from_index(num_elts, index, maxdim, verbose=False):
    op = op_from_index(num_elts, index)
    return find_best_gens_crs(op, maxdim, verbose=verbose)


