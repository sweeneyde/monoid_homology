from monoid_homology.resolution import (
    FiniteMonoidRingProjectiveResolution as Res,
    partial_smithify,
    get_kernel_basis,
    FreeAbelianSubmodule,
)
from monoid_homology import (
    adjoin_1,
)
from random import randrange, shuffle

def test_right_mul_matrix_to_Z_matrix():
    op = [[0,1,0,1,0],[0,1,0,1,1],[2,3,2,3,2],[2,3,2,3,3],[0,1,2,3,4]]
    # ZS1 x00 <-- ZS1
    # Multiplication *(x10 - x00)
    resolution = Res(op)

    assert set(resolution.e_to_Lclass.keys()) == {0, 1, 4}
    assert resolution.e_to_Lclass[0] == (0, 2)
    assert resolution.e_to_Lclass[1] == (1, 3)
    assert resolution.e_to_Lclass[4] == (0, 1, 2, 3, 4)

    M, _ = resolution.right_mul_matrix_to_Z_matrix(
        input_gens=[4],
        output_gens=[0],
        right_mul_matrix=[[[(+1, 2), (-1, 0)]]]
    )
    # M kills everything except the identity.
    assert M == [
        [0, 0, 0, 0, -1],
        [0, 0, 0, 0, +1],
    ]

def test_kernel_basis():
    assert get_kernel_basis([[1, 0],[0, 1]], 2) == []
    assert get_kernel_basis([[2, 0],[0, 3]], 2) == []
    assert get_kernel_basis([[2, 0],[0, 0]], 2) == [[0, 1]]
    assert get_kernel_basis([[0, 0],[0, 2]], 2) == [[1, 0]]
    assert get_kernel_basis([[0, 0],[0, 0]], 2) == [[1, 0], [0, 1]]
    assert get_kernel_basis([[1, 2],
                             [1, 2]], 2) == [[-2, 1]]
    assert get_kernel_basis([[1, 1],
                             [2, 2]], 2) == [[-1, 1]]
    assert get_kernel_basis([[1, 0, 0],
                             [0, 1, 0]], 3) == [[0, 0, 1]]
    assert get_kernel_basis([[2,2,2],
                             [3,3,3]], 3) == [[-1, 1, 0], [-1, 0, 1]]
    assert get_kernel_basis([], 0) == []
    assert get_kernel_basis([[]], 0) == []
    assert get_kernel_basis([[],[]], 0) == []
    assert get_kernel_basis([], 1) == [[1]]
    assert get_kernel_basis([], 2) == [[1, 0], [0, 1]]
    assert get_kernel_basis([[ 0,-1,-1],
                             [-1, 0,+1],
                             [+1,+1, 0]], 3) == [[1, -1, 1]]
    assert get_kernel_basis([[ 0,-1,-3],
                             [-2, 0,+3],
                             [+2,+1, 0]], 3) == [[-3, 6, -2]]

def test_which_are_in_integer_span():
    def which(N, spanners, queries):
        mod = FreeAbelianSubmodule(N)
        for v in spanners:
            mod.add(v)
        return [q for q in queries if q in mod]

    queries = [[5],[4],[3],[2],[1],[0]]
    assert which(1, [[0]], queries) == [[0]]
    assert which(1, [[1]], queries) == queries
    assert which(1, [[2]], queries) == [[4], [2], [0]]
    assert which(1, [[3]], queries) == [[3], [0]]
    assert which(1, [[5]], queries) == [[5], [0]]
    assert which(1, [[10], [12]], queries) == [[4], [2], [0]]

    fives = [[0],[5],[10],[15],[20],[25],[30]]
    assert which(1, [[60], [150], [100]], fives) == [[0], [10], [20], [30]]

    vec2 = [[x,y] for x in range(-5, 10) for y in range(-5, 10)]
    assert which(2, [[1,0],
                     [0,1]], vec2) == [[x, y] for [x, y] in vec2]
    assert which(2, [[2,2],
                     [3,3]], vec2) == [[x, y] for [x, y] in vec2 if x == y]
    assert which(2, [[2,3],
                     [0,1]], vec2) == [[x, y] for [x, y] in vec2 if x % 2 == 0]
    assert which(2, [[2,3],
                     [0,5]], vec2) == [[x, y] for [x, y] in vec2 if x % 2 == 0 and y % 5 == (x//2*3) % 5]
    assert which(2, [[0,2],
                     [0,3],
                     [0,5]], vec2) == [[x, y] for [x, y] in vec2 if x == 0]
    assert which(2, [[-1,1],
                      [0,5]], vec2) == [[x, y] for [x, y] in vec2 if (x + y) % 5 == 0]

def test_echelon():
    def echelon(N, rows):
        mod = FreeAbelianSubmodule(N)
        for v in rows:
            mod.add(v)
        return mod.basis
    assert echelon(2, [[161, 161], [100, 100]]) == [[1, 1]]
    assert echelon(2, [[161, 161], [100, 100]]) == [[1, 1]]
    assert echelon(2, [[1, 0], [0, 1]]) == [[1, 0], [0, 1]]
    assert echelon(2, [[1, 2], [3, 5]]) == [[1, 2], [0, -1]]
    assert echelon(2, [[0, 1], [1, 0]]) == [[1, 0], [0, 1]]
    assert echelon(3, [[1, 1, 1], [0, 0, 2], [0, 0, 3]]) == [[1, 1, 1], [0, 0, 1]]
    assert echelon(100, []) == []
    assert echelon(0, [[], [], [], []]) == [] # empty vector is zero vector


def test_cover_rect22():
    op = [[0,1,0,1,0],[0,1,0,1,1],[2,3,2,3,2],[2,3,2,3,3],[0,1,2,3,4]]
    resolution = Res(op)

    # This fails if we do the one-pass approach.
    # If everything is in the kernel, cover it with the identity map.
    input_gens, right_mul_matrix = resolution.cover([4], [[1,0,0,0,0],
                                                          [0,1,0,0,0],
                                                          [0,0,1,0,0],
                                                          [0,0,0,1,0],
                                                          [0,0,0,0,1]])
    assert input_gens == [4]
    assert right_mul_matrix == [[[(1, 4)]]]

    for cover_method in [resolution.cover, resolution.cover_fast]:
        # If only semigroup elements 0 and 2 are in the kernel, cover with
        # exactly that ideal.
        input_gens, right_mul_matrix = cover_method([4], [[1,0,0,0,0],
                                                          [0,0,1,0,0]])
        assert input_gens == [0]
        assert right_mul_matrix == [[[(1, 0)]]]

        # Same with {1, 3}, except ZS(e0)(e1) = ZS(e1)(e1)
        # so minimality chooses ZS(e0).
        input_gens, right_mul_matrix = cover_method([4], [[0,1,0,0,0],
                                                          [0,0,0,1,0]])
        assert input_gens == [0]
        assert right_mul_matrix == [[[(1, 1)]]]

        # For {0, 1, 2, 3}, cover by direct sum of the above.
        input_gens, right_mul_matrix = cover_method([4], [[1,0,0,0,0],
                                                          [0,1,0,0,0],
                                                          [0,0,1,0,0],
                                                          [0,0,0,1,0]])
        assert input_gens == [0, 0]
        assert right_mul_matrix == [[[(1, 0)],[(1, 1)]]]

        # If there's no kernel, can extend with the zero module
        input_gens, right_mul_matrix = cover_method([0, 0], [])
        assert input_gens == []
        assert right_mul_matrix == [[], []]

def test_cover_Zmod2():
    op = [[0,1],[1,0]]
    resolution = Res(op)

    for cover_method in [resolution.cover, resolution.cover_fast]:
        # The kernel of augmentation is <g-e> Cover it.
        input_gens, right_mul_matrix = cover_method([0], [[-1, 1]])
        assert input_gens == [0]
        assert right_mul_matrix == [[[(-1, 0), (1, 1)]]]


        # The kernel of multiplication by g-e is <e+g>. Cover it.
        input_gens, right_mul_matrix = cover_method([0], [[1, 1]])
        assert input_gens == [0]
        assert right_mul_matrix == [[[(1, 0), (1, 1)]]]

def test_cover_Zmod8():
    op = [[(i+j)%8 for j in range(8)] for i in range(8)]
    resolution = Res(op)

    for cover_method in [resolution.cover, resolution.cover_fast]:
        # The kernel of augmentation is Z<g-e, gg-g, ggg-gg, ..., ggggggg-gggggg>
        # But this is really just ZS<g-e>
        input_gens, right_mul_matrix = cover_method([0], [[-1,1,0,0,0,0,0,0],
                                                          [0,-1,1,0,0,0,0,0],
                                                          [0,0,-1,1,0,0,0,0],
                                                          [0,0,0,-1,1,0,0,0],
                                                          [0,0,0,0,-1,1,0,0],
                                                          [0,0,0,0,0,-1,1,0],
                                                          [0,0,0,0,0,0,-1,1]])
        assert input_gens == [0]
        assert right_mul_matrix == [[[(-1, 0), (1, 1)]]]

        # The above map "*(g-e)" has kernel the norm element.
        input_gens, right_mul_matrix = cover_method([0], [[1,1,1,1,1,1,1,1]])
        assert input_gens == [0]
        assert right_mul_matrix == [[[(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]]]


def test_extend_Zmod2():
    op = [[0,1],[1,0]]
    resolution = Res(op)
    resolution.extend(4)
    assert resolution.module_list == [[0],[0],[0],[0],[0]]
    assert resolution.right_mul_matrices == [
        None,
        [[[(-1, 0), (1, 1)]]],
        [[[(1, 0), (1, 1)]]],
        [[[(-1, 0), (1, 1)]]],
        [[[(1, 0), (1, 1)]]],
    ]

def test_extend_rect22():
    op = [[0,1,0,1,0],[0,1,0,1,1],[2,3,2,3,2],[2,3,2,3,3],[0,1,2,3,4]]
    resolution = Res(op)
    resolution.extend(10)
    assert resolution.module_list == [[0], [4], [0, 0], [], [], [], [], [], [], [], []]
    assert resolution.right_mul_matrices == [
        None,
        [[[(-1, 0), (1, 2)]]],
        [[[(1, 0)], [(1, 1)]]],
        [[], []],
        [],
        [],
        [],
        [],
        [],
        [],
        [],
    ]

def test_extend_Zmod8():
    op = [[(i+j)%8 for j in range(8)] for i in range(8)]
    resolution = Res(op)
    resolution.extend(10)
    assert resolution.module_list == [[0]] * 11
    assert resolution.right_mul_matrices == [
        None,
        [[[(-1, 0), (1, 1)]]],
        [[[(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]]],
        [[[(-1, 0), (1, 1)]]],
        [[[(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]]],
        [[[(-1, 0), (1, 1)]]],
        [[[(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]]],
        [[[(-1, 0), (1, 1)]]],
        [[[(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]]],
        [[[(-1, 0), (1, 1)]]],
        [[[(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)]]],
    ]

def test_extend_rect33():
    op = [[3*(i//3)+j%3 for j in range(9)] for i in range(9)]
    for i, row in enumerate(op):
        row.append(i)
    op.append(list(range(10)))

    resolution = Res(op)
    resolution.extend(10)
    assert resolution.module_list == [[0], [9, 9], [0, 0, 0, 0, 0, 0], [], [], [], [], [], [], [], []]
    assert resolution.right_mul_matrices == [
        None,
        [[[(-1, 0), (1, 3)], [(-1, 0), (1, 6)]]],
        [
            [[(1,0)],[(1,1)],[(1,2)],[],[],[]],
            [[],[],[],[(1,0)],[(1,1)],[(1,2)]],
        ],
        [[], [], [], [], [], []],
        [],
        [],
        [],
        [],
        [],
        [],
        [],
    ]

def test_sympy_rational_homology_ranks():
    from monoid_homology import op_from_id
    table_ranks = [
        ((3, 10),   [1, 0, 0, 0]),
        ((4, 123),  [1, 0, 1, 0]),
        ((5, 917),  [1, 0, 1, 1]),
        ((5, 1142), [1, 0, 1, 0]),
        ((6, 8713), [1, 0, 1, 2]),
        ((6, 15870), [1, 0, 0, 1]),
    ]
    for (nelements, ix), expected in table_ranks:
        op = op_from_id(nelements, ix)
        resolution = Res(adjoin_1(op))
        assert resolution.sympy_rational_homology_ranks(3) == expected

def test_FreeAbelianSubmodule_random():
    for N in [0, 1, 2, 3, 4, 5, 10, 20]:
        for _ in range(10):
            mod = FreeAbelianSubmodule(N)
            mod.assert_consistent()
            vecs = [
                [randrange(-10, 10) for _ in range(N)]
                for _ in range(randrange(N + 2))
            ]
            vec0 = vecs[0] if vecs else [0]*N
            for vec in vecs:
                mod.add(vec)
                mod.assert_consistent()
                assert vec in mod
                assert [-x for x in vec] in mod
                assert [10*x for x in vec] in mod
                assert [x+y for x, y in zip(vec0, vec)] in mod


def test_FreeAbelianSubmodule_ordering():
    for N in [0,1,2,3,4,5,10,20]:
        for _ in range(3):
            vecs = [
                [randrange(-10, 10) for _ in range(N)]
                for _ in range(randrange(N + 2))
            ]
            mod0 = FreeAbelianSubmodule(N)
            for vec in vecs:
                mod0.add(vec)
            for _ in range(10):
                mod1 = FreeAbelianSubmodule(N)
                shuffle(vecs)
                for vec in vecs:
                    mod1.add(vec)
                    assert mod1 <= mod0
                    assert mod1 < mod0 or mod1 == mod0
                assert mod1 == mod0

def test_FreeAbelianSubmodule_deletion():
    for N in [0,1,2,3,4,5,10,20]:
        for _ in range(3):
            vecs = [
                [randrange(-10, 10) for _ in range(N)]
                for _ in range(randrange(N + 2))
            ]
            mod0 = FreeAbelianSubmodule(N)
            for vec in vecs:
                mod0.add(vec)

            for _ in range(3):
                # make a proper submodule by deleting a single vector
                mod1 = FreeAbelianSubmodule(N)
                basis1 = list(map(list.copy, mod0.basis))
                if not basis1:
                    continue
                removed = basis1.pop(randrange(len(basis1)))
                for vec in basis1:
                    mod1.add(vec)

                assert removed not in mod1
                for vec1 in mod1.basis:
                    vec1_removed = [x+y for x, y in zip(vec1, removed)]
                    assert vec1_removed not in mod1
                all_sum = list(map(sum,zip(*mod0.basis)))
                assert all_sum not in mod1

                assert mod1 < mod0
                assert mod1 + mod0 == mod0

            for _ in range(3):
                # make a proper submodule by deleting two vectors
                mod1 = FreeAbelianSubmodule(N)
                basis1 = list(map(list.copy, mod0.basis))
                if len(basis1) <= 1:
                    continue
                removed1 = basis1.pop(randrange(len(basis1)))
                removed2 = basis1.pop(randrange(len(basis1)))
                removed = [(2*x-5*y) for x, y in zip(removed1, removed2)]
                complement = [-3*x+8*y for x, y in zip(removed1, removed2)]
                for vec in basis1:
                    mod1.add(vec)

                assert removed1 not in mod1
                assert removed2 not in mod1
                assert removed not in mod1
                assert complement not in mod1

                deleted = FreeAbelianSubmodule(N)
                deleted.add(removed)
                deleted.add(complement)

                also_deleted = FreeAbelianSubmodule(N)
                also_deleted.add(removed1)
                also_deleted.add(removed2)

                assert also_deleted == deleted
                assert deleted + mod1 == mod0
                assert also_deleted + mod1 == mod0

def test_FreeAbelianSubmodule_coefficients():
    for N in [0,1,2,3,4,5,10,20]:
        for _ in range(3):
            vecs = [
                [randrange(-10, 10) for _ in range(N)]
                for _ in range(randrange(N + 2))
            ]
            mod = FreeAbelianSubmodule(N)
            for vec in vecs:
                mod.add(vec)

            for _ in range(3):
                coefficients = [randrange(-100, 100) for _ in range(len(mod.basis))]
                element = [0] * N
                for a, v in zip(coefficients, mod.basis):
                    for i in range(N):
                        element[i] += a * v[i]
                assert mod.get_coefficients(element) == coefficients
