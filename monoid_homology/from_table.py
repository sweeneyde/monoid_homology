"""
Manipulating finite semigroups by their multiplication table.
"""

from itertools import combinations, permutations
from functools import cache
from pathlib import Path
import string

from .knuth_bendix import kb_normalize
from .crs import CRS

DATA_DIR = Path(__file__).parent.parent / "finite_semigroup_data"

SYMBOLS = string.ascii_uppercase + string.ascii_lowercase + string.digits


@cache
def all_op_strings(num_elts):
    filename = DATA_DIR / f"{int(num_elts)}elt_semis.txt"
    # print(f"Loading from {filename}...", end='')
    with open(filename, "r") as f:
        lines = f.readlines()
    # print("done")
    return lines

def string_to_op(s):
    return [list(map(int, row)) for row in s.rstrip().split(";")]

def all_ops(num_elts):
    if num_elts == 0:
        return ([],)
    return map(string_to_op, all_op_strings(num_elts))

def op_from_id(num_elts, index):
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

import random

def sample_permutations(arr):
    n2 = len(arr) // 2
    early, late = arr[:n2], arr[n2:]
    yield early + late
    yield early + late[::-1]
    yield early[::-1] + late
    yield early[::-1] + late[::-1]
    yield late + early
    yield late + early[::-1]
    yield late[::-1] + early
    yield late[::-1] + early[::-1]
    for _ in range(10):
        arr1 = list(arr)
        random.shuffle(arr1)
        yield tuple(arr1)


def crs_from_gens(op, gens, extra):
    rep = representation_by_generators(op, gens)
    if rep is None:
        return
    alphabet = ''.join(SYMBOLS[g] for g in gens)
    if extra >= 1 and len(gens) < len(op):
        if extra >= 2:
            perms = permutations(alphabet)
        else:
            perms = set(sample_permutations(alphabet))
    else:
        perms = [alphabet]

    for ordering in map(''.join, perms):
        pairs = relation_str_pairs(op, rep, ordering, gens)
        alphabet, pairs = kb_normalize(ordering, pairs) # this should terminate?
        yield CRS(alphabet, pairs)


def find_best_gens_crs(op, maxdim, verbose=False, extra=0):
    """
    Brute search to find the set of generators
    that make for the smallest essential chain complex from the CRS.
    """
    n = len(op)

    cost_best_crs, best_crs = None, None
    for num_gens in range(0, n + 1):
        for gens in combinations(range(n), num_gens):
            for crs in crs_from_gens(op, gens, extra):
                lengths = crs.essential_counts(maxdim + 1)
                if verbose:
                    print(gens, lengths)
                # total size of boundary matrices
                cost = sum(a*b for a, b in zip(lengths, lengths[1:]))
                if best_crs is None or cost < cost_best_crs:
                    cost_best_crs, best_crs = cost, crs
    if verbose:
        print("Best:", best_crs.alphabet, best_crs.essential_counts(maxdim + 1))
    return best_crs

