from itertools import combinations

from monoid_homology import (
    CRS,
    all_ops,
    op_from_id,
    find_best_gens_crs,
    kb_normalize,
)

from monoid_homology.from_table import (
    string_to_op,
    representation_by_generators,
    all_gens_crs,
    crs_from_gens,
)

from monoid_homology.knuth_bendix import (
    kb_complete
)

import pytest

def test_crs_homology():
    # Uses Sympy because it's hard to set up CI for SAGE.

    trivial = CRS("", [])
    assert trivial.sympy_rational_homology_ranks(4) == [1, 0, 0, 0, 0]

    NxN = CRS("xy", [("yx", "xy")])
    assert NxN.sympy_rational_homology_ranks(3) == [1, 2, 1, 0]

    NxNxN = CRS("xyz", [("yx", "xy"), ("zx", "xz"), ("zy", "yz")])
    assert NxNxN.sympy_rational_homology_ranks(3) == [1, 3, 3, 1]

    Z = CRS("xy", [("xy", ""), ("yx", "")])
    assert Z.sympy_rational_homology_ranks(3) == [1, 1, 0, 0]

    Free2 = CRS("xy", [])
    assert Free2.sympy_rational_homology_ranks(3) == [1, 2, 0, 0]

    Z3 = CRS("x", [("xxx", "")])
    assert Z3.sympy_rational_homology_ranks(3) == [1, 0, 0, 0]

    # Rectangular bands
    rect22 = CRS("xy", [("xx", "x"), ("yy", "y"), ("xyx", "x"), ("yxy", "y")])
    assert rect22.sympy_rational_homology_ranks(4) == [1, 0, 1, 0, 0]

    rect33 = CRS("xyz", [(a+a, a) for a in "xyz"] +
                        [(a+b+a, a) for (a, b) in "xy xz yx yz zx zy".split()] +
                        [(a+b+c, a+c) for (a, b, c) in "xyz xzy yxz yzx zxy zyx".split()])
    assert rect33.sympy_rational_homology_ranks(3) == [1, 0, 4, 0]


def test_crs_essentials():
    rect22 = CRS("xy", [("xx", "x"), ("yy", "y"), ("xyx", "x"), ("yxy", "y")])
    rect22.compute_essentials(3)
    for dim, ess_set in {
        0: {()},
        1: {("x",), ("y",)},
        2: {("x", "x"), ("x", "yx"), ("y", "y"), ("y", "xy")},
        3: {
            ("x", "x", "x"), ("x", "x", "yx"),
            ("y", "y", "y"), ("y", "y", "xy"),
            ("x", "yx", "y"), ("x", "yx", "x"),
            ("y", "xy", "y"), ("y", "xy", "x"),
        }
    }.items():
        assert set(rect22.essentials[dim]) == ess_set

    Z = CRS("xy", [("xy", ""), ("yx", "")])
    Z.compute_essentials(3)
    for dim, ess_set in {
        0: {()},
        1: {("x",), ("y",)},
        2: {("x", "y"), ("y", "x")},
        3: {("x", "y", "x"), ("y", "x", "y")},
    }.items():
        assert set(Z.essentials[dim]) == ess_set

def all_ops():
    assert all_ops(1) == [
        [[0]]
    ]
    assert all_ops(2) == [
        [[0, 0], [0, 0]],
        [[0, 1], [1, 0]],
        [[0, 0], [0, 1]],
        [[0, 0], [1, 1]]
    ]
    assert all_ops(3) == [
        [[0, 0, 0], [0, 0, 0], [0, 0, 0]],
        [[0, 0, 2], [0, 0, 2], [2, 2, 0]],
        [[0, 1, 1], [1, 0, 0], [1, 0, 0]],
        [[0, 0, 0], [0, 0, 0], [0, 0, 1]],
        [[0, 0, 0], [0, 0, 0], [0, 0, 2]],
        [[0, 0, 0], [0, 0, 0], [0, 1, 2]],
        [[0, 0, 0], [0, 0, 0], [2, 2, 2]],
        [[0, 0, 0], [0, 0, 1], [0, 1, 2]],
        [[0, 0, 2], [0, 0, 2], [2, 2, 2]],
        [[0, 1, 0], [1, 0, 1], [0, 1, 2]],
        [[0, 1, 2], [1, 0, 2], [2, 2, 2]],
        [[0, 0, 0], [0, 1, 0], [0, 0, 2]],
        [[0, 0, 0], [0, 1, 0], [2, 2, 2]],
        [[0, 0, 0], [0, 1, 1], [0, 1, 2]],
        [[0, 0, 0], [0, 1, 1], [0, 2, 2]],
        [[0, 0, 0], [0, 1, 2], [2, 2, 2]],
        [[0, 0, 0], [1, 1, 1], [2, 2, 2]],
        [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
    ]
    for n in (1, 2, 3):
        for op in all_ops(n):
            for i in range(n):
                for j in range(n):
                    for k in range(n):
                        assert op[op[i][j]][k] == op[i][op[j][k]]

def test_op_from_id():
    assert op_from_id(2, 1) == [[0, 0], [0, 0]]

def all_gens_crs():
    z3 = all_gens_crs([[(i+j)%3 for i in range(3)] for j in range(3)])
    z3.compute_essentials(3)
    assert z3.alphabet == "ABC"
    assert set(z3.relations) == {("AA", "A"), ("AB", "B"), ("AC", "C"),
                                 ("BA", "B"), ("BB", "C"), ("BC", "A"),
                                 ("CA", "C"), ("CB", "A"), ("CC", "B")}
    assert set(z3.essentials[0]) == {()}
    assert set(z3.essentials[1]) == {("A",), ("B",), ("C",)}
    assert set(z3.essentials[2]) == {(i, j) for i in "ABC" for j in "ABC"}

    rect22 = all_gens_crs([[(i&2) | (j&1) for j in range(4)] for i in range(4)])
    assert rect22.alphabet == "ABCD"
    assert set(rect22.essentials[0]) == {()}
    assert set(rect22.essentials[1]) == {(i,) for i in "ABCD"}
    assert set(rect22.essentials[1]) == {(i, j) for i in "ABCD" for j in "ABCD"}

def test_crs_from_gens():
    z3_op = [[(i+j)%3 for i in range(3)] for j in range(3)]
    # 0 doesn't generate Z/3Z.
    assert list(crs_from_gens(z3_op, [0], extra=0)) == []

    [z3_1] = crs_from_gens(z3_op, [1], extra=0)
    assert z3_1.alphabet == "B"
    assert set(z3_1.rules) == {("BBBB", "B")}
    z3_1.compute_essentials(3)
    assert set(z3_1.essentials[1]) == {("B",)}
    assert set(z3_1.essentials[2]) == {("B", "BBB")}
    assert set(z3_1.essentials[3]) == {("B", "BBB", "B")}

    [z3_01] = crs_from_gens(z3_op, [0, 1], extra=0)
    assert z3_01.alphabet == "AB"
    assert set(z3_01.rules) == {("BBB", "A"), ("AB", "B"), ("BA", "B"), ("AA", "A")}
    z3_01.compute_essentials(3)
    assert set(z3_01.essentials[1]) == {("A",), ("B",)}
    assert set(z3_01.essentials[2]) == {("A", "A"), ("A", "B"), ("B", "BB"), ("B", "A")}
    assert set(z3_01.essentials[3]) == {("A", "A", "A"), ("A", "A", "B"),
                                        ("A", "B", "BB"), ("A", "B", "A"),
                                        ("B", "BB", "B"), ("B", "BB", "A"),
                                        ("B", "A", "B"), ("B", "A", "A")}


def test_all_gen_sets_give_same_ranks():
    table_ranks = [
        ((3, 10),   [1, 0, 0, 0]),
        ((4, 123),  [1, 0, 1, 0]),
        ((5, 917),  [1, 0, 1, 1]),
        ((5, 1142), [1, 0, 1, 0]),
        ((6, 8713), [1, 0, 1, 2]),
        ((6, 15870), [1, 0, 0, 1]),
    ]
    for (n, i), ranks in table_ranks:
        op = op_from_id(n, i)
        for num_gens in range(0, n + 1):
            for gens in combinations(range(n), num_gens):
                for crs in crs_from_gens(op, gens, extra=0):
                    assert crs.sympy_rational_homology_ranks(3) == ranks
        assert find_best_gens_crs(op, 3).sympy_rational_homology_ranks(3) == ranks

def test_kb_eliminate_redundant_generators():
    # Make sure to normalize so no single-letters are reducible.

    # Direct test
    assert kb_normalize("AB", [("B", "A")]) == ("A", [])

    # Make sure that "B" gets deleted in this odd situation
    rules = [
        ('AA', 'A'), ('AB', 'A'), ('AC', 'A'),
        ('BA', 'A'), ('BB', 'A'), ('BC', 'B'),
        ('CA', 'A'), ('CB', 'B'), ('CC', 'A')
    ]
    assert kb_complete(rules[:]) == [('AA', 'A'), ('AC', 'A'), ('CA', 'A'), ('CC', 'A'), ('B', 'A')]
    assert kb_normalize('ABC', rules[:]) == ('AC', [('AA', 'A'), ('AC', 'A'), ('CA', 'A'), ('CC', 'A')])

    # The example that caught the bug
    find_best_gens_crs([[0, 0, 0], [0, 0, 1], [0, 1, 0]], maxdim=4, extra=2)

def test_non_noetherian():
    crs = CRS("ABC", [("ABB", "ABA"), ("AC", "BCC")], max_rewrites=10_000)
    culprit = "ABBC"
    # ABBC
    # ABAC
    # ABBCC
    # ABACC
    # ABBCCC
    # ABACCC
    # ABBCCCC
    # ABACCCC
    # ...
    msg = f"No fixed point was found for {culprit} after 10000 iterations"
    with pytest.raises(RuntimeError, match=msg):
        crs.reduce(culprit)
