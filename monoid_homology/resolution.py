import operator
from bisect import bisect

def xgcd(a, b):
    # Maintain the invariants:
    #          x * a +      y * b ==      g
    #     next_x * a + next_y * b == next_g
    # Do the Euclidean algorithm to (g, next_g),
    # but carry the rest of the equations along for the ride.
    x, next_x = 1, 0
    y, next_y = 0, 1
    g, next_g = a, b
    while next_g:
        q = g // next_g
        x, next_x = next_x, x - q * next_x
        y, next_y = next_y, y - q * next_y
        g, next_g = next_g, g - q * next_g
    if g < 0:
        x, y, g = -x, -y, -g
    return x, y, g

def make_identity(n):
    row = [0]*n
    M = [row[:] for _ in range(n)]
    for i in range(n):
        M[i][i] = 1
    return M

def sort_rows(matrix):
    def sortkey(row):
        for i, x in enumerate(row):
            if x:
                return i, abs(x)
        return (len(row),)
    matrix.sort(key=sortkey)


def partial_smithify(A, num_cols, *, need_S=False, need_T=False):
    """
    Given a matrix A, find a matrix D of the same shape
    where D is nonzero only on its main diagonal,
    and such that SAT = D.

    This isn't Smith Normal Form because I don't have
    any divisibility requirements for D.

    Compute S, T, and their inverses, only if requested.
    """
    for row in A:
        assert len(row) == num_cols
    D = [row.copy() for row in A]
    m = len(D)
    n = num_cols
    rm = range(m)
    rn = range(n)

    if need_S:
        S = make_identity(m)
    else:
        sort_rows(D)

    if need_T:
        T = make_identity(n)

    def row_op(i1, i2, z):
        Di1, Di2 = D[i1], D[i2]
        for jj in rn:
            Di2[jj] += z*Di1[jj]
        if need_S:
            Si1, Si2 = S[i1], S[i2]
            for jj in rm:
                Si2[jj] += z*Si1[jj]

    def col_op(j1, j2, z):
        for ii in rm:
            Dii = D[ii]
            Dii[j2] += z*Dii[j1]
        if need_T:
            for ii in rn:
                Tii = T[ii]
                Tii[j2] += z*Tii[j1]

    def row_swap(i1, i2):
        Di1, Di2 = D[i1], D[i2]
        Di1[:], Di2[:] = Di2[:], Di1[:]
        if need_S:
            Si1, Si2 = S[i1], S[i2]
            Si1[:], Si2[:] = Si2[:], Si1[:]

    def col_swap(j1, j2):
        for Dii in D:
            Dii[j1], Dii[j2] = Dii[j2], Dii[j1]
        if need_T:
            for Tii in T:
                Tii[j1], Tii[j2] = Tii[j2], Tii[j1]

    def generalized_row_op(i1, i2, x, y, z, w):
        Di1, Di2 = D[i1], D[i2]
        for jj in rn:
            aa = Di1[jj]
            bb = Di2[jj]
            Di1[jj] = x*aa + y*bb
            Di2[jj] = z*aa + w*bb
        if need_S:
            Si1, Si2 = S[i1], S[i2]
            for jj in rm:
                aa = Si1[jj]
                bb = Si2[jj]
                Si1[jj] = x*aa + y*bb
                Si2[jj] = z*aa + w*bb

    def generalized_col_op(j1, j2, x, y, z, w):
        for Dii in D:
            aa = Dii[j1]
            bb = Dii[j2]
            Dii[j1] = x * aa + y * bb
            Dii[j2] = z * aa + w * bb
        if need_T:
            for Tii in T:
                aa = Tii[j1]
                bb = Tii[j2]
                Tii[j1] = x * aa + y * bb
                Tii[j2] = z * aa + w * bb

    def improve_with_row_ops(i1, i2, j):
        a = D[i1][j]
        b = D[i2][j]
        if b == 0:
            return
        elif a == 0:
            row_swap(i1, i2)
            # assert D[i1][j] == b
            # assert D[i2][j] == 0
        elif b % a == 0:
            row_op(i1, i2, -b//a)
            # assert D[i1][j] == a
            # assert D[i2][j] == 0
        elif a % b == 0:
            row_swap(i1, i2)
            row_op(i1, i2, -a//b)
            # assert D[i1][j] == b
            # assert D[i2][j] == 0
        else:
            x, y, g = xgcd(a, b)
            generalized_row_op(i1, i2, x, y, -b//g, a//g);
            # assert D[i1][j] == g
            # assert D[i2][j] == 0

    def improve_with_col_ops(j1, j2, i):
        a = D[i][j1]
        b = D[i][j2]
        if b == 0:
            return
        elif a == 0:
            col_swap(j1, j2)
            # assert D[i][j1] == b
            # assert D[i][j2] == 0
        elif b % a == 0:
            col_op(j1, j2, -b // a)
            # assert D[i][j1] == a
            # assert D[i][j2] == 0
        elif a % b == 0:
            col_swap(j1, j2)
            col_op(j1, j2, -a // b)
            # assert D[i][j1] == b
            # assert D[i][j2] == 0
        else:
            x, y, g = xgcd(a, b)
            generalized_col_op(j1, j2, x, y, -b//g, a//g)
            # assert D[i][j1] == g
            # assert D[i][j2] == 0

    if min(m, n) > 100:
        from tqdm import tqdm
        range_mn = tqdm(range(min(m,n)), desc=f"SNF", dynamic_ncols=True, smoothing=0.0, ascii=True, miniters=0)
    else:
        range_mn = range(min(m,n))

    # make diagonal
    for k in range_mn:
        while True:
            for i in range(k+1, m):
                improve_with_row_ops(k, i, k)
            if all(D[k][j] == 0 for j in range(k+1, n)):
                break
            for j in range(k+1, n):
                improve_with_col_ops(k, j, k)
            if all(D[i][k] == 0 for i in range(k+1, m)):
                break

    # Don't bother fixing the divisibility
    result = {"D": D}
    if need_S:
        result["S"] = S
    if need_T:
        result["T"] = T
    return result

def get_kernel_basis(A, num_cols):
    for row in A:
        assert len(row) == num_cols
    m = len(A)
    n = num_cols
    smith_A = partial_smithify(A, n, need_T=True)
    D = smith_A["D"]
    T = smith_A["T"]
    ker_D_indices = [j for j in range(n) if j >= m or D[j][j] == 0]
    columns = [
        [T[i][j] for i in range(n)]
        for j in ker_D_indices
    ]
    sort_rows(columns)
    return columns

class FreeAbelianSubmodule:
    __slots__ = ["N",
                 "basis",
                 "pivot_location_in_column",
                 "pivot_location_in_row",
                 ]

    def __init__(self, ambient_dimension, vectors):
        N = ambient_dimension
        assert set(map(len, vectors)) <= {N}
        basis = list(map(list, vectors))
        basis.sort(key=lambda row: [abs(x) for x in row], reverse=True)
        M = len(basis)

        pivot_location_in_column = [None] * N
        pivot_location_in_row = [None] * M

        if not basis:
            self.N = N
            self.basis = basis
            self.pivot_location_in_column = pivot_location_in_column
            self.pivot_location_in_row = pivot_location_in_row
            return

        # Put in row echelon form with row operations
        i1 = 0
        basis_i1 = basis[i1]
        for j in range(N):
            # for i2 in range(i1 + 1, M):
            #     basis_i2 = basis[i2]
            for basis_i2 in basis[i1+1:]:
                # Do row operations to make basis_i2[j] == 0
                a = basis_i1[j]
                b = basis_i2[j]
                if b == 0:
                    pass
                elif a == 0:
                    basis_i1[:], basis_i2[:] = basis_i2[:], basis_i1[:]
                elif b % a == 0:
                    q = b // a
                    for jj in range(j, N):
                        basis_i2[jj] -= q * basis_i1[jj]
                elif a % b == 0:
                    basis_i1[:], basis_i2[:] = basis_i2[:], basis_i1[:]
                    q = a // b
                    for jj in range(j, N):
                        basis_i2[jj] -= q * basis_i1[jj]
                else:
                    x, y, g = xgcd(a, b)
                    ag = a//g
                    mbg = -b//g
                    for jj in range(j, N):
                        aa = basis_i1[jj]
                        bb = basis_i2[jj]
                        basis_i1[jj] = x*aa + y*bb
                        basis_i2[jj] = mbg*aa + ag*bb
                assert basis_i2[j] == 0

            if basis_i1[j] != 0:
                # We have a nonzero entry in this column, so it's a pivot.
                pivot_location_in_column[j] = i1
                pivot_location_in_row[i1] = j
                i1 += 1
                if i1 == M:
                    break
                basis_i1 = basis[i1]

        del basis[i1:]
        del pivot_location_in_row[i1:]
        assert None not in pivot_location_in_row
        self.N = N
        self.basis = basis
        self.pivot_location_in_column = pivot_location_in_column
        self.pivot_location_in_row = pivot_location_in_row
        # self.assert_consistent()

    def assert_consistent(self):
        basis = self.basis
        for i, j in enumerate(self.pivot_location_in_row):
            assert basis[i][j] != 0
            for jj in range(j):
                assert basis[i][jj] == 0
        for j, i in enumerate(self.pivot_location_in_column):
            if i is not None:
                assert basis[i][j] != 0, (basis, i, j)
                for ii in range(i+1, len(self.basis)):
                    assert basis[ii][j] == 0

    def __contains__(self, vec0):
        vec = vec0
        col_piv = self.pivot_location_in_column
        N = self.N
        basis = self.basis
        for j in range(N):
            if vec[j] != 0:
                p = col_piv[j]
                if p is None:
                    # can't zero this vec entry out
                    # without disrupting previous parts
                    return False
                a = basis[p][j]
                b = vec[j]
                if b % a != 0:
                    # This pivot can't zero this entry
                    return False
                else:
                    if vec is vec0:
                        vec = vec.copy()
                    q = b // a
                    row = basis[p]
                    assert set(vec[:j]) <= {0}
                    for jj in range(j, N):
                        vec[jj] -= q * row[jj]
        return True

    def add(self, vec):
        col_piv = self.pivot_location_in_column
        row_piv = self.pivot_location_in_row
        N = self.N
        basis = self.basis
        assert len(vec) == N
        # vec = vec.copy()
        for j in range(N):
            if vec[j] != 0:
                p = col_piv[j]
                if p is None:
                    # This vector gets inserted so that its first entry is a pivot.
                    where = bisect(row_piv, j)
                    basis.insert(where, vec)
                    row_piv.insert(where, j)
                    col_piv[j] = where
                    for ii in range(where + 1, len(basis)):
                        # assert col_piv[row_piv[ii]] == ii - 1
                        col_piv[row_piv[ii]] = ii
                    # self.assert_consistent()
                    return
                row = basis[p]
                a = row[j]
                b = vec[j]
                # assert a != 0
                # assert b != 0
                if b % a == 0:
                    q = b // a
                    for jj in range(j, N):
                        vec[jj] -= q * row[jj]
                elif a % b == 0:
                    row[:], vec[:] = vec[:], row[:]
                    q = a // b
                    for jj in range(j, N):
                        vec[jj] -= q * row[jj]
                else:
                    x, y, g = xgcd(a, b)
                    ag = a//g
                    mbg = -b//g
                    for jj in range(j, N):
                        aa = row[jj]
                        bb = vec[jj]
                        row[jj] = x*aa + y*bb
                        vec[jj] = mbg*aa + ag*bb
                assert vec[j] == 0
        # making it to the end means that vec has been zeroed out.
        # nothing more needs to be done.
        assert not any(vec)
        # self.assert_consistent()

class FiniteMonoidRingProjectiveResolution:
    __slots__ = ["op", "identity", "e_to_Lclass", "module_list", "right_mul_matrices"]

    def __init__(self, op: list[list[int]]):
        self.op = op
        n = len(op)
        rn = range(n)
        E = {x for x in rn if op[x][x] == x}
        [identity] = [e for e in E if all(op[e][x] == x == op[x][e] for x in rn)]
        self.identity = identity

        Lclass_to_e = {}
        for e in [identity] + sorted(E - {identity}):
            Lclass = tuple(sorted({op[x][e] for x in rn}))
            if Lclass not in Lclass_to_e:
                Lclass_to_e[Lclass] = e
        self.e_to_Lclass = {e: L for (L, e) in Lclass_to_e.items()}

        # Augmentation from a small left ideal
        min_e, min_L = min(self.e_to_Lclass.items(), key=lambda e_L: len(e_L[1]))
        dim0_gens = [min_e]
        self.module_list = [dim0_gens]
        self.right_mul_matrices = [None]

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
                                 algorithm='auto')
                for dim in range(0, up_to_dimension + 1)}

    def homology_list(self, up_to_dimension, **kwargs):
        h = self.homology(up_to_dimension, **kwargs)
        return [h[i] for i in range(1, up_to_dimension + 1)]

    def SAGE_chain_complex(self, up_to_dimension, check=True, verbose=False, sparse=True, base_ring=None):
        self.extend(up_to_dimension)
        # local imports so the rest can be run in vanilla Python without SAGE
        from sage.all import ZZ, Matrix, ChainComplex
        ig0 = operator.itemgetter(0)
        if base_ring is None:
            base_ring = ZZ
        matrices = {}
        for dim in range(1, up_to_dimension + 1):
            m = len(self.module_list[dim - 1])
            n = len(self.module_list[dim])
            M = Matrix(base_ring, m, n, sparse=sparse)
            right_mul_matrix = self.right_mul_matrices[dim]
            for i, row in enumerate(right_mul_matrix):
                for j, cell in enumerate(row):
                    M[i,j] = sum(map(ig0, cell))
            matrices[dim] = M
        return ChainComplex(matrices, degree_of_differential=-1, check=check, base_ring=base_ring)

    def sympy_rational_homology_ranks(self, up_to_dimension):
        self.extend(up_to_dimension + 1)
        # SAGE is more efficient because it delegates to PARI,
        # but we can at least get the ranks without anything fancy.
        # local imports so the rest can be run in vanilla Python without sympy
        from sympy.matrices import Matrix
        boundary_ranks = {}
        ig0 = operator.itemgetter(0)
        for dim in range(1, up_to_dimension + 2):
            m = len(self.module_list[dim - 1])
            n = len(self.module_list[dim])
            M = Matrix.zeros(m, n)
            right_mul_matrix = self.right_mul_matrices[dim]
            for i, row in enumerate(right_mul_matrix):
                for j, cell in enumerate(row):
                    M[i,j] = sum(map(ig0, cell))
            boundary_ranks[dim] = M.rank()
        return [
            (len(self.module_list[dim])
                - boundary_ranks.get(dim, 0) # only count cycles
                - boundary_ranks.get(dim + 1, 0) # kill off boundaries
                )
            for dim in range(up_to_dimension + 1)]

    def extend(self, up_to_dimension):
        while len(self.module_list) < up_to_dimension + 1:
            self.extend_once()

    def extend_once(self):
        if len(self.module_list) == 1:
            [last_gens] = self.module_list
            [min_e] = last_gens
            min_L = self.e_to_Lclass[min_e]
            # Augmentation
            Z_matrix = [[1] * len(min_L)]
            width = len(min_L)
        else:
            second_to_last_gens, last_gens = self.module_list[-2:]
            Z_matrix, width = self.right_mul_matrix_to_Z_matrix(last_gens, second_to_last_gens, self.right_mul_matrices[-1])
        kernel_basis = get_kernel_basis(Z_matrix, width)
        del Z_matrix
        input_gens, right_mul_matrix = self.cover(last_gens, kernel_basis)
        self.module_list.append(input_gens)
        self.right_mul_matrices.append(right_mul_matrix)

    def right_mul_matrix_to_Z_matrix(self, input_gens, output_gens, right_mul_matrix):
        assert len(right_mul_matrix) == len(output_gens), (self.module_list, self.right_mul_matrices)
        for row in right_mul_matrix:
            assert len(row) == len(input_gens)
            for cell in row:
                for term in cell:
                    assert len(term) == 2
                    assert isinstance(term[0], int)
                    assert isinstance(term[1], int)
        input_index_pairs = [(j, jj) for j, gen in enumerate(input_gens) for jj in range(len(self.e_to_Lclass[gen]))]
        output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(self.e_to_Lclass[gen]))]
        input_index_pair_to_index = {x: i for i, x in enumerate(input_index_pairs)}
        output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
        matrix = [[0] * len(input_index_pairs) for _ in output_index_pairs]

        for j, x in enumerate(input_gens):
            for i, y in enumerate(output_gens):
                right_mul = right_mul_matrix[i][j]
                for jj, xx in enumerate(self.e_to_Lclass[x]):
                    input_index = input_index_pair_to_index[j,jj]
                    for coeff, m in right_mul:
                        yy = self.op[xx][m]
                        ii = self.e_to_Lclass[y].index(yy)
                        output_index = output_index_pair_to_index[i,ii]
                        matrix[output_index][input_index] += coeff
        row_length = len(input_index_pairs)
        return matrix, row_length

    def cover(self, output_gens, kernel_basis):
        if len(kernel_basis) == 0:
            input_gens = []
            right_mul_matrix = [[] for _ in range(len(output_gens))]
            return input_gens, right_mul_matrix

        output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(self.e_to_Lclass[gen]))]
        output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
        N = len(output_index_pairs)

        # imagine covering ZSk <--(k)--- ZS for each kernel generator k.
        # Record the image of each of these.
        # Note that these necessarily live in the kernel because
        # kernels of R-module homomorphism are necessarily
        # fixed by R.

        def left_multiply_index(s, index):
            # Takes a one-hot Z-basis vector at index
            # and multiplies it on the left by the semigroup element s
            # to find the index of the result one-hot Z-basis vector
            (i, ii) = output_index_pairs[index]
            Lclass = self.e_to_Lclass[output_gens[i]]
            x = Lclass[ii]
            sx = self.op[s][x]
            ii_new = Lclass.index(sx)
            return output_index_pair_to_index[i, ii_new]
        left_multiply_index_table = [
            [left_multiply_index(s, index) for index in range(N)]
            for s in range(len(self.op))
        ]

        def left_multiply_vector(s, vec):
            result = [0] * len(vec)
            for out_index, x in zip(left_multiply_index_table[s], vec):
                result[out_index] += x
            return result

        input_gens = []
        right_mul_columns = []
        covered = FreeAbelianSubmodule(N, [])

        if len(kernel_basis) > 100:
            from tqdm import tqdm
            kernel_basis = tqdm(kernel_basis, desc=f"dim{len(self.module_list)}", dynamic_ncols=True, smoothing=0.0, ascii=True, miniters=0)
        for vec in kernel_basis:
            if vec not in covered:
                e = self.identity
                for s in range(len(self.op)):
                    svec = left_multiply_vector(s, vec)
                    covered.add(svec)
                    if s in self.e_to_Lclass and svec == vec:
                        if len(self.e_to_Lclass[s]) < len(self.e_to_Lclass[e]):
                            e = s
                input_gens.append(e)
                right_mul_column = [[] for _ in output_gens]
                for index, coeff in enumerate(vec):
                    if coeff:
                        i, ii = output_index_pairs[index]
                        Lclass = self.e_to_Lclass[output_gens[i]]
                        m = Lclass[ii]
                        right_mul_column[i].append((coeff, m))
                right_mul_columns.append(right_mul_column)
        del covered

        assert len(right_mul_columns) == len(input_gens)
        for col in right_mul_columns:
            assert len(col) == len(output_gens)
        right_mul_matrix = [
            [right_mul_columns[j][i] for j in range(len(input_gens))]
            for i in range(len(output_gens))
        ]
        assert len(right_mul_matrix) == len(output_gens)

        return input_gens, right_mul_matrix

def find_good_resolution(op0, peek_dim=4):
    """Choose a few different versions of a monoid operation,
    and compute some projective resolutions up to `peek_dim`.
    Return the smallest one.
    """
    n = len(op0)
    n_1 = n - 1
    rn = range(n)
    ops = [
        [[op0[i][j] for j in rn] for i in rn],
        [[op0[j][i] for j in rn] for i in rn],
        [[n_1 - op0[n_1 - i][n_1 - j] for j in rn] for i in rn],
        [[n_1 - op0[n_1 - j][n_1 - i] for j in rn] for i in rn],
    ]
    resolutions = [FiniteMonoidRingProjectiveResolution(op) for op in ops]
    while len(resolutions[0].module_list) - 1 < peek_dim:
        for res in resolutions:
            res.extend_once()
            if len(res.module_list[-1]) == 0:
                print("short circuit: finite resolution!")
                return res
    print([len(res.module_list[-1]) for res in resolutions])
    return min(resolutions, key=lambda res: len(res.module_list[-1]))
