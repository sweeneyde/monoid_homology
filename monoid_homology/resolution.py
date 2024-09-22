import operator

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

def partial_smithify(A, num_cols, *, need_S=False, need_T=False, need_Sinv=False, need_Tinv=False):
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
    if need_Sinv:
        Sinv = make_identity(m)
    if need_T:
        T = make_identity(n)
    if need_Tinv:
        Tinv = make_identity(n)

    def generalized_row_op(i1, i2, x, y, z, w):
        assert x * w - y * z == 1
        for jj in range(n):
            aa = D[i1][jj]
            bb = D[i2][jj]
            D[i1][jj] = x*aa + y*bb
            D[i2][jj] = z*aa + w*bb
        if need_S:
            for jj in range(m):
                aa = S[i1][jj]
                bb = S[i2][jj]
                S[i1][jj] = x*aa + y*bb
                S[i2][jj] = z*aa + w*bb
        if need_Sinv:
            for jj in range(m):
                aa = Sinv[jj][i1]
                bb = Sinv[jj][i2]
                Sinv[jj][i1] = w*aa - z*bb
                Sinv[jj][i2] = x*bb - y*aa

    def generalized_col_op(j1, j2, x, y, z, w):
        for ii in range(m):
            aa = D[ii][j1]
            bb = D[ii][j2]
            D[ii][j1] = x * aa + y * bb
            D[ii][j2] = z * aa + w * bb
        if need_T:
            for ii in range(n):
                aa = T[ii][j1]
                bb = T[ii][j2]
                T[ii][j1] = x*aa + y*bb
                T[ii][j2] = z*aa + w*bb
        if need_Tinv:
            for ii in range(n):
                aa = Tinv[j1][ii]
                bb = Tinv[j2][ii]
                Tinv[j1][ii] = w*aa - z*bb
                Tinv[j2][ii] = x*bb - y*aa

    def improve_with_row_ops(i1, i2, j):
        a = D[i1][j]
        b = D[i2][j]
        if b == 0:
            return
        elif a != 0 and b % a == 0:
            q = b // a
            generalized_row_op(i1, i2, 1, 0, -q, 1)
            assert D[i1][j] == a
            assert D[i2][j] == 0
        else:
            x, y, g = xgcd(a, b)
            generalized_row_op(i1, i2, x, y, -b//g, a//g);
            assert D[i1][j] == g
            assert D[i2][j] == 0

    def improve_with_col_ops(j1, j2, i):
        a = D[i][j1]
        b = D[i][j2]
        if b == 0:
            return
        elif a != 0 and b % a == 0:
            q = b // a
            generalized_col_op(j1, j2, 1, 0, -q, 1)
            assert D[i][j1] == a
            assert D[i][j2] == 0
        else:
            x, y, g = xgcd(a, b)
            generalized_col_op(j1, j2, x, y, -b//g, a//g)
            assert D[i][j1] == g
            assert D[i][j2] == 0

    # make diagonal
    for k in range(min(m, n)):
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
    if need_Sinv:
        result["Sinv"] = Sinv
    if need_T:
        result["T"] = T
    if need_Tinv:
        result["Tinv"] = Tinv
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
    columns.sort(key=lambda col: [abs(x) for x in col], reverse=True)
    return columns

def which_are_in_integer_span(basis, vector_size, queries):
    for col in basis:
        assert len(col) == vector_size
    if len(queries) == 0:
        return []
    M = [
        [basis[j][i] for j in range(len(basis))]
        for i in range(vector_size)
    ]
    m = len(M)
    n = len(basis)

    # y in span(basis)
    # iff  y in im(M)
    # iff  y in im(Sinv D Tinv)
    # iff  y in im(Sinv D)
    # iff  y = Sinv D x  for some x
    # iff  S y = D x     for some x
    # iff  S y in im(D)

    smith_M = partial_smithify(M, n, need_S=True)
    D = smith_M["D"]
    S = smith_M["S"]
    ed = [D[k][k] if k < n else 0 for k in range(m)]
    assert len(ed) == m
    assert len(S) == m

    result = []
    for y in queries:
        nonzero_y_indexes = [i for i, entry in enumerate(y) if entry]
        result_i = True
        for row, d in zip(S, ed):
            Sy_entry = 0
            for i in nonzero_y_indexes:
                Sy_entry += row[i]*y[i]
            # assert Sy_entry == sum(map(operator.mul, row, y))
            if d == 0:
                if Sy_entry != 0:
                    result_i = False
                    break
            else:
                if Sy_entry % d != 0:
                    result_i = False
                    break
        result.append(result_i)

    return result

def compressed_basis(spanners):
    """
    Given a list of vectors, produce
    a hopefully shorter list of vectors with
    the same span.
    """
    # use "row_ops"
    M = [list(row) for row in spanners]
    M.sort(key=lambda row: [abs(x) for x in row], reverse=True)
    if not M:
        return M
    n = len(M[0])
    m = len(M)
    for row in M:
        assert len(row) == n

    def improve_with_row_ops(i1, i2, j):
        Mi1, Mi2 = M[i1], M[i2]
        a, b = Mi1[j], Mi2[j]
        if b == 0:
            pass
        elif a != 0 and b % a == 0:
            q = b // a
            for jj in range(n):
                Mi2[jj] -= q * Mi1[jj]
        else:
            x, y, g = xgcd(a, b)
            ag = a//g
            mbg = -b//g
            for jj in range(n):
                aa = Mi1[jj]
                bb = Mi2[jj]
                Mi1[jj] = x*aa + y*bb
                Mi2[jj] = mbg*aa + ag*bb
        assert Mi2[j] == 0

    i1 = 0
    for j in range(n):
        for i2 in range(i1 + 1, m):
            improve_with_row_ops(i1, i2, j)
        if M[i1][j] != 0:
            i1 += 1
            if i1 == m:
                break

    return [row for row in M if any(row)]

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
                                 algorithm=algorithm)
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

        def left_multiply_vector(s, vec):
            result = [0 for _ in vec]
            for index, x in enumerate(vec):
                result[left_multiply_index(s, index)] += x
            return result

        def get_ZS_span(vec):
            span = set()
            for s in range(len(self.op)):
                svec = left_multiply_vector(s, vec)
                span.add(tuple(svec))
            return compressed_basis(span)
            # return sorted(span)

        ZS_spans = [get_ZS_span(vec) for vec in kernel_basis]

        already_covered_kindexes = set()
        already_covered = [] # in the Z-basis
        input_gens = []
        right_mul_columns = []

        while True:
            if len(kernel_basis) == 0:
                break
            inclusions = [
                [None] * len(kernel_basis)
                for _ in range(len(kernel_basis))
            ]
            not_already_covered_kindexes = set(range(len(kernel_basis))) - already_covered_kindexes
            for kindex1, row in enumerate(inclusions):
                for kindex2 in already_covered_kindexes:
                    row[kindex2] = True
                row[kindex1] = True
                not_covered_kindexes = sorted(not_already_covered_kindexes - {kindex1})
                not_already_covered_vecs = [kernel_basis[kindex2] for kindex2 in not_covered_kindexes]
                which = which_are_in_integer_span(already_covered + ZS_spans[kindex1], N, not_already_covered_vecs)
                for included, kindex2 in zip(which, not_covered_kindexes):
                    row[kindex2] = included
                assert None not in row

            # inclusions = [
            #     which_are_in_integer_span(already_covered + ZS_spans[kindex], N, kernel_basis)
            #     for kindex in range(len(kernel_basis))
            # ]
            inclusion_counts = [sum(row) for row in inclusions]
            max_inclusion_count = max(inclusion_counts)
            kindex_e_pairs = []
            for kindex, kernel_basis_vec in enumerate(kernel_basis):
                if inclusion_counts[kindex] != max_inclusion_count:
                    continue
                # Now see if we can replace
                #       image <--(k)--- ZS
                # with something smaller but with the same image, like
                #       image <--(k)--- Zse
                # This requires that ZSk == ZSek, so k == ek
                for e in self.e_to_Lclass:
                    if left_multiply_vector(e, kernel_basis_vec) == kernel_basis_vec:
                        kindex_e_pairs.append((kindex, e))
            kindex, e = min(kindex_e_pairs, key=lambda kindex_e: len(self.e_to_Lclass[kindex_e[1]]))

            already_covered_kindexes.update([i for i in range(len(kernel_basis)) if inclusions[kindex][i]])
            input_gens.append(e)
            already_covered += ZS_spans[kindex]
            already_covered = compressed_basis(already_covered)

            right_mul_column = [[] for _ in output_gens]
            # The multiplier is k
            for index, coeff in enumerate(kernel_basis[kindex]):
                if coeff:
                    i, ii = output_index_pairs[index]
                    Lclass = self.e_to_Lclass[output_gens[i]]
                    m = Lclass[ii]
                    right_mul_column[i].append((coeff, m))
            right_mul_columns.append(right_mul_column)

            if all(inclusions[kindex]):
                # covered everything!
                break

        assert len(right_mul_columns) == len(input_gens)
        for col in right_mul_columns:
            assert len(col) == len(output_gens)
        right_mul_matrix = [
            [right_mul_columns[j][i] for j in range(len(input_gens))]
            for i in range(len(output_gens))
        ]
        assert len(right_mul_matrix) == len(output_gens)

        return input_gens, right_mul_matrix
