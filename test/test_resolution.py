from monoid_homology.resolution import (
    FiniteMonoidRingProjectiveResolution as Res,
    partial_smithify,
    get_kernel_basis,
    which_are_in_integer_span,
    compressed_basis,
)
from monoid_homology import (
    adjoin_1,
)

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

def test_smith():
    import random
    ids = [
        [[int(i==j) for j in range(n)] for i in range(n)]
        for n in (0,1,2,3,4)
    ]
    def matmul(A, nA, B, nB):
        for row in A:
            assert len(row) == nA
        for row in B:
            assert len(row) == nB
        assert nA == len(B)
        return [
            [sum(A[i][k]*B[k][j] for k in range(nA)) for j in range(nB)]
            for i in range(len(A))
        ]

    for m in (0,1,2,3,4):
        for n in (0,1,2,3,4):
            for _ in range(3):
                A = [[random.randint(-10, 10) for _ in range(n)]
                     for _ in range(m)]
                smith_A = partial_smithify(A, num_cols=n,
                                           need_S=True, need_Sinv=True,
                                           need_T=True, need_Tinv=True)
                D = smith_A["D"]
                S, Sinv = smith_A["S"], smith_A["Sinv"]
                T, Tinv = smith_A["T"], smith_A["Tinv"]

                assert len(D) == len(A) == m
                assert all(len(row)==n for row in D)
                assert len(S) == len(Sinv) == m
                assert all(len(row) == m for row in S)
                assert all(len(row) == m for row in Sinv)
                assert len(T) == len(Tinv) == n
                assert all(len(row) == n for row in T)
                assert all(len(row) == n for row in Tinv)

                assert matmul(S, m, Sinv, m) == ids[m]
                assert matmul(Sinv, m, S, m) == ids[m]
                assert matmul(T, n, Tinv, n) == ids[n]
                assert matmul(Tinv, n, T, n) == ids[n]

                assert matmul(S, m, matmul(A, n, T, n), n) == D
                assert matmul(Sinv, m, matmul(D, n, Tinv, n), n) == A

                for i, row in enumerate(D):
                    for j, x in enumerate(row):
                        if x != 0:
                            assert i == j

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
                             [+2,+1, 0]], 3) == [[3, -6, 2]]

def test_which_are_in_integer_span():
    queries = [(55,[5]),(44,[4]),(33,[3]),(22,[2]),(11,[1]),(0,[0])]
    which = which_are_in_integer_span
    assert which([[0]], 1, queries) == {0}
    assert which([[1]], 1, queries) == {0, 11, 22, 33, 44, 55}
    assert which([[2]], 1, queries) == {0, 22, 44}
    assert which([[3]], 1, queries) == {0, 33}
    assert which([[5]], 1, queries) == {0, 55}
    assert which([[10], [12]], 1, queries) == {0, 22, 44}

    fives = [(0,[0]),(5,[5]),(10,[10]),(15,[15]),(20,[20]),(25,[25]),(30,[30])]
    assert which([[60], [150], [100]], 1, fives) == {0, 10, 20, 30}

    vec2 = [((x,y), [x, y]) for x in range(-5, 10) for y in range(-5, 10)]
    assert which([[1,0],
                  [0,1]], 2, vec2) == {(x, y) for (x, y), _ in vec2}
    assert which([[2,2],
                  [3,3]], 2, vec2) == {(x, y) for (x, y), _ in vec2 if x == y}
    assert which([[2,3],
                  [0,1]], 2, vec2) == {(x, y) for (x, y), _ in vec2 if x % 2 == 0}
    assert which([[2,3],
                  [0,5]], 2, vec2) == {(x, y) for (x, y), _ in vec2 if x % 2 == 0 and y % 5 == (x//2*3) % 5}
    assert which([[0,2],
                  [0,3],
                  [0,5],], 2, vec2) == {(x, y) for (x, y), _ in vec2 if x == 0}
    assert which([[-1,1],
                  [0,5],], 2, vec2) == {(x, y) for (x, y), _ in vec2 if (x + y) % 5 == 0}

def test_compressed_basis():
    assert compressed_basis([[161, 161], [100, 100]]) == [[1, 1]]
    assert compressed_basis([[1, 0], [0, 1]]) == [[1, 0], [0, 1]]
    assert compressed_basis([[1, 2], [3, 5]]) == [[1, 2], [0, 1]]
    assert compressed_basis([[0, 1], [1, 0]]) == [[1, 0], [0, 1]]
    assert compressed_basis([[1, 1, 1], [0, 0, 2], [0, 0, 3]]) == [[1, 1, 1], [0, 0, 1]]
    assert compressed_basis([]) == []
    assert compressed_basis([[], [], [], []]) == [] # empty vector is zero vector

def test_cover_rect22():
    op = [[0,1,0,1,0],[0,1,0,1,1],[2,3,2,3,2],[2,3,2,3,3],[0,1,2,3,4]]
    resolution = Res(op)

    # If everything is in the kernel, cover it with the identity map.
    input_gens, right_mul_matrix = resolution.cover([4], [[1,0,0,0,0],
                                                          [0,1,0,0,0],
                                                          [0,0,1,0,0],
                                                          [0,0,0,1,0],
                                                          [0,0,0,0,1]])
    assert input_gens == [4]
    assert right_mul_matrix == [[[(1, 4)]]]

    # If only semigroup elements 0 and 2 are in the kernel, cover with
    # exactly that ideal.
    input_gens, right_mul_matrix = resolution.cover([4], [[1,0,0,0,0],
                                                          [0,0,1,0,0]])
    assert input_gens == [0]
    assert right_mul_matrix == [[[(1, 0)]]]

    # Same with {1, 3}, except ZS(e0)(e1) = ZS(e1)(e1)
    # so minimality chooses ZS(e0).
    input_gens, right_mul_matrix = resolution.cover([4], [[0,1,0,0,0],
                                                          [0,0,0,1,0]])
    assert input_gens == [0]
    assert right_mul_matrix == [[[(1, 1)]]]

    # For {0, 1, 2, 3}, cover by direct sum of the above.
    input_gens, right_mul_matrix = resolution.cover([4], [[1,0,0,0,0],
                                                          [0,1,0,0,0],
                                                          [0,0,1,0,0],
                                                          [0,0,0,1,0]])
    assert input_gens == [0, 0]
    assert right_mul_matrix == [[[(1, 0)],[(1, 1)]]]

    # If there's no kernel, can extend with the zero module
    input_gens, right_mul_matrix = resolution.cover([0, 0], [])
    assert input_gens == []
    assert right_mul_matrix == [[], []]

def test_cover_Zmod2():
    op = [[0,1],[1,0]]
    resolution = Res(op)

    # The kernel of augmentation is <g-e> Cover it.
    input_gens, right_mul_matrix = resolution.cover([0], [[-1, 1]])
    assert input_gens == [0]
    assert right_mul_matrix == [[[(-1, 0), (1, 1)]]]

    # The kernel of multiplication by g-e is <e+g>. Cover it.
    input_gens, right_mul_matrix = resolution.cover([0], [[1, 1]])
    assert input_gens == [0]
    assert right_mul_matrix == [[[(1, 0), (1, 1)]]]

def test_cover_Zmod8():
    op = [[(i+j)%8 for j in range(8)] for i in range(8)]
    resolution = Res(op)

    # The kernel of augmentation is Z<g-e, gg-g, ggg-gg, ..., ggggggg-gggggg>
    # But this is really just ZS<g-e>
    input_gens, right_mul_matrix = resolution.cover([0], [[-1,1,0,0,0,0,0,0],
                                                          [0,-1,1,0,0,0,0,0],
                                                          [0,0,-1,1,0,0,0,0],
                                                          [0,0,0,-1,1,0,0,0],
                                                          [0,0,0,0,-1,1,0,0],
                                                          [0,0,0,0,0,-1,1,0],
                                                          [0,0,0,0,0,0,-1,1]])
    assert input_gens == [0]
    assert right_mul_matrix == [[[(-1, 0), (1, 1)]]]

    # The above map "*(g-e)" has kernel the norm element.
    input_gens, right_mul_matrix = resolution.cover([0], [[1,1,1,1,1,1,1,1]])
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

def test_extend_Rect22():
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