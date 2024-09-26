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
    columns.sort(key=lambda col: [abs(x) for x in col], reverse=True)
    return columns

def which_are_in_integer_span(basis, vector_size, queries):
    # for col in basis:
    #     assert len(col) == vector_size
    # for index, vector in queries:
    #     assert len(vector) == vector_size
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

    result = set()
    for index, y, nonzero_y_indexes in queries:
        for row, d in zip(S, ed):
            Sy_entry = 0
            for i in nonzero_y_indexes:
                Sy_entry += row[i]*y[i]
            if d == 0:
                if Sy_entry != 0:
                    break
            else:
                if Sy_entry % d != 0:
                    break
        else: # no break
            result.add(index)
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
        elif a == 0:
            Mi1[:], Mi2[:] = Mi2[:], Mi1[:]
        elif b % a == 0:
            q = b // a
            for jj in range(n):
                Mi2[jj] -= q * Mi1[jj]
        elif a % b == 0:
            Mi1[:], Mi2[:] = Mi2[:], Mi1[:]
            q = a // b
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
            result = [0 for _ in vec]
            for out_index, x in zip(left_multiply_index_table[s], vec):
                result[out_index] += x
            return result

        def get_ZS_span(vec):
            span = set()
            for s in range(len(self.op)):
                svec = left_multiply_vector(s, vec)
                span.add(tuple(svec))
            return compressed_basis(span)

        ZS_spans = [get_ZS_span(vec) for vec in kernel_basis]

        kindex_to_e = []
        for vec in kernel_basis:
            usable_es = [e for e in self.e_to_Lclass if left_multiply_vector(e, vec) == vec]
            e = min(usable_es, key=lambda e: len(self.e_to_Lclass[e]))
            kindex_to_e.append(e)
        nonzero_kernel_basis_indices = [
            [i for i, x in enumerate(k) if x]
            for k in kernel_basis
        ]

        base_inclusions = []
        for kindex in range(len(kernel_basis)):
            queries = [
                (kindex, k, nonzero_kernel_basis_indices[kindex])
                for kindex, k in enumerate(kernel_basis)
            ]
            included = which_are_in_integer_span(ZS_spans[kindex], N, queries)
            assert kindex in included
            base_inclusions.append(included)

        kindexes_in_covering_order = sorted(
            range(len(kernel_basis)),
            key=lambda kindex: len(base_inclusions[kindex]),
            reverse=True
        )

        already_covered_kindexes = set()
        already_covered  = []
        input_gens = []
        right_mul_columns = []

        def add_summand(kindex):
            already_covered_kindexes.update(inclusions[kindex])
            already_covered.extend(ZS_spans[kindex])
            input_gens.append(kindex_to_e[kindex])
            right_mul_column = [[] for _ in output_gens]
            for index, coeff in enumerate(kernel_basis[kindex]):
                if coeff:
                    i, ii = output_index_pairs[index]
                    Lclass = self.e_to_Lclass[output_gens[i]]
                    m = Lclass[ii]
                    right_mul_column[i].append((coeff, m))
            right_mul_columns.append(right_mul_column)

        while True:
            inclusions = {kindex: base_inclusions[kindex] | already_covered_kindexes
                          for kindex in kindexes_in_covering_order
                          if kindex not in already_covered_kindexes}
            for kindex, to_be_included in inclusions.items():
                new_span = already_covered + ZS_spans[kindex]
                in_question = [kindex2 for kindex2 in range(len(kernel_basis)) if kindex2 not in to_be_included]
                queries = [(kindex2, kernel_basis[kindex2], nonzero_kernel_basis_indices[kindex2]) for kindex2 in in_question]
                which = which_are_in_integer_span(new_span, N, queries)
                to_be_included.update(which)

            # try to maximize the "efficiency": the number of kernel basis elements
            # covered per new Z-rank added
            kindex = max(
                inclusions.keys(),
                key=lambda kindex: len(inclusions[kindex]) / len(self.e_to_Lclass[kindex_to_e[kindex]])
            )
            num_added = len(self.e_to_Lclass[kindex_to_e[kindex]])
            num_covered = len(inclusions[kindex]) - len(already_covered_kindexes)
            efficiency = num_covered / num_added - 0.0001

            add_summand(kindex)
            if len(already_covered_kindexes) == len(kernel_basis):
                # covered everything!
                break

            for kindex, to_be_included in inclusions.items():
                # Attempt at a "lower bound" on num_covered.
                # Adding this kindex will result in at least `to_be_included`
                # being covered. The uncertainty is that it could already
                # have been covered by a previous addition, though then
                # that previously-added vector's efficiency was greater than expected,
                # so the average efficiency is still valid.
                # On the other hand, interacting with the existing cover
                # means that we could actually cover more, so it's probably a good thing to include.
                num_covered_approx = len(to_be_included - already_covered_kindexes)
                num_added = len(self.e_to_Lclass[kindex_to_e[kindex]])
                if num_covered_approx / num_added >= efficiency:
                    # print("got one for cheap.")
                    add_summand(kindex)

            if len(already_covered_kindexes) == len(kernel_basis):
                # covered everything!
                break

            already_covered = compressed_basis(already_covered)

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
