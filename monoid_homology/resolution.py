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

def partial_smithify(A, num_cols, verbose=False):
    """
    Given an integer matrix A, find a matrix D of the same shape
    where D is nonzero only on its main diagonal, and there are
    invertible matrices S and T such that SAT=D.
    Also produce the matrix T.

    This isn't Smith Normal Form because I don't have
    any divisibility requirements for D.
    """
    for row in A:
        assert len(row) == num_cols
    D = [row.copy() for row in A]
    m = len(D)
    n = num_cols

    # T starts as the identity.
    T = [[0] * n for _ in range(n)]
    for i in range(n):
        T[i][i] = 1

    def improve_with_row_ops(i1, i2, j):
        Di1, Di2 = D[i1], D[i2]
        a = Di1[j]
        b = Di2[j]
        if b == 0:
            return
        elif a == 0:
            Di1[:], Di2[:] = Di2[:], Di1[:]
            # assert Di1[j] == b
            # assert Di2[j] == 0
        elif b % a == 0:
            q = -b // a
            for jj in range(j, n):
                Di2[jj] += q*Di1[jj]
            # assert Di1[j] == a
            # assert Di2[j] == 0
        elif a % b == 0:
            q = -(a // b)
            Di1[:], Di2[:] = Di2[:], Di1[:]
            for jj in range(j, n):
                Di2[jj] += q*Di1[jj]
            # assert Di1[j] == b
            # assert Di2[j] == 0
        else:
            x, y, g = xgcd(a, b)
            mbg = -b // g
            ag = a//g
            for jj in range(j, n):
                aa = Di1[jj]
                bb = Di2[jj]
                Di1[jj] = x*aa + y*bb
                Di2[jj] = mbg*aa + ag*bb
            # assert Di1[j] == g
            # assert Di2[j] == 0

    def improve_with_col_ops(j1, j2, i):
        a = D[i][j1]
        b = D[i][j2]
        if b == 0:
            return
        elif a == 0:
            for Dii in D:
                Dii[j1], Dii[j2] = Dii[j2], Dii[j1]
            for Tii in T:
                Tii[j1], Tii[j2] = Tii[j2], Tii[j1]
            # assert D[i][j1] == b
            # assert D[i][j2] == 0
        elif b % a == 0:
            q = -b // a
            for Dii in D:
                Dii[j2] += q*Dii[j1]
            for Tii in T:
                Tii[j2] += q*Tii[j1]
            # assert D[i][j1] == a
            # assert D[i][j2] == 0
        elif a % b == 0:
            q = -a // b
            for Dii in D:
                Dii[j1], Dii[j2] = Dii[j2], Dii[j1]
                Dii[j2] += q*Dii[j1]
            for Tii in T:
                Tii[j1], Tii[j2] = Tii[j2], Tii[j1]
                Tii[j2] += q*Tii[j1]
            # assert D[i][j1] == b
            # assert D[i][j2] == 0
        else:
            x, y, g = xgcd(a, b)
            mbg = -b // g
            ag = a // g
            for Dii in D:
                aa = Dii[j1]
                bb = Dii[j2]
                Dii[j1] = x * aa + y * bb
                Dii[j2] = mbg * aa + ag * bb
            for Tii in T:
                aa = Tii[j1]
                bb = Tii[j2]
                Tii[j1] = x * aa + y * bb
                Tii[j2] = mbg * aa + ag * bb
            # assert D[i][j1] == g
            # assert D[i][j2] == 0

    if verbose and min(m, n) > 100:
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
    return D, T

def vec_sort_key(vec):
    for i, x in enumerate(vec):
        if x:
            return i, abs(x)
    return (len(vec),)

def get_kernel_basis(A, num_cols, verbose=False):
    for row in A:
        assert len(row) == num_cols
    m = len(A)
    n = num_cols
    D, T = partial_smithify(A, n, verbose)
    ker_D_indices = [j for j in range(n) if j >= m or D[j][j] == 0]
    columns = [
        [T[i][j] for i in range(n)]
        for j in ker_D_indices
    ]
    columns.sort(key=vec_sort_key)
    return columns


class FreeAbelianSubmodule:
    """
    A submodule of ZZ^n, with a basis stored as row-vectors is row-echelon form.

    Mutable, so we can relatively quickly add in the spans of new vectors.
    """
    __slots__ = ["N",
                 "basis",
                 "pivot_location_in_column",
                 "pivot_location_in_row"]

    def __init__(self, ambient_dimension):
        self.N = N = ambient_dimension
        self.pivot_location_in_column = [None] * N
        self.pivot_location_in_row = []
        self.basis = []

    def assert_consistent(self):
        """assert we're in in row_echelon form"""
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
        """Does this subspace contain this vector?"""
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
                    # assert set(vec[:j]) <= {0}
                    for jj in range(j, N):
                        vec[jj] -= q * row[jj]
        return True

    def add(self, vec):
        col_piv = self.pivot_location_in_column
        row_piv = self.pivot_location_in_row
        N = self.N
        basis = self.basis
        assert len(vec) == N
        vec = vec.copy()
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
                # assert vec[j] == 0
        # making it to the end means that vec has been zeroed out.
        # nothing more needs to be done.
        # assert not any(vec)
        # self.assert_consistent()

    def copy(self):
        new = object.__new__(type(self))
        new.N = self.N
        new.basis = list(map(list.copy, self.basis))
        new.pivot_location_in_column = self.pivot_location_in_column.copy()
        new.pivot_location_in_row = self.pivot_location_in_row.copy()
        return new

    def __iadd__(self, other):
        if not isinstance(other, FreeAbelianSubmodule):
            return NotImplemented
        if self.N != other.N:
            raise ValueError(f"Ambient dimension mismatch: {self.N} != {other.N}")
        for vec in other.basis:
            self.add(vec)
        return self

    def __add__(self, other):
        if len(self.basis) < len(other.basis):
            small, large = self, other
        else:
            small, large = other, self
        large = large.copy()
        large += small
        return large

    __radd__ = __add__

    def __le__(self, other):
        return all(map(other.__contains__, self.basis))

    def __lt__(self, other):
        return all(map(other.__contains__, self.basis)) and not all(map(self.__contains__, other.basis))

    def __eq__(self, other):
        return all(map(other.__contains__, self.basis)) and all(map(self.__contains__, other.basis))



class FiniteMonoidRingProjectiveResolution:
    """
    A projective resolution of the trivial module ZZ over the monoid ring ZZ[S],
    where S is some monoid.

    The module Xd in dimension d is represented by module_list[d]:
    module_list[d] is a list of idempotents (e1, ..., en) in S,
    and we interpret this to mean

        Xd := ZZ[S]e1 (+) ... (+) ZZ[S]en.

    This is a projective module because each ZZ[S] = ZZ[S]e_i (+) ZZ[S](1-e_i).

    The the map Xd --> X{d-1}
    is a map ZZ[S]e1 (+) ... (+) ZZ[S]en --> ZZ[S]f1 (+) ... (+) ZZ[S]fm
    and is a direct sum of elementary maps ZZ[S]e_j --> ZZ[S]f_i
    where each elementary map is right-multiplication by some element k of ZZ[S].
    The these k-values are stored in right_mul_matrices[d][i][j],
    and each k-value is a list of pairs (ZZ_coefficient, S_element).

    To compute the homology group H_d(BS) = Tor^ZZ[S]_d(Z, Z),
    we need to tensor our complex with ZZ.
    Note that tensors distribute across direct sums,
    and that ZZ (x)_S ZZ[S]e = ZZ (x)_S ZZe = ZZ,
    so each direct summand becomes a copy of ZZ.
    The monoid maps ZZ[S]e_j --k--> ZZ[S]f_i
    become the augmentation of the element k,
    so these augmentations become the entries of the matrices
    in the tensor with ZZ.
    """
    __slots__ = ["op", "e_to_Lclass", "module_list", "right_mul_matrices"]

    def __init__(self, op: list[list[int]]):
        """Given the monoid operation table, start a resolution ZZ <--- ZZ[S]e"""
        self.op = op
        n = len(op)
        rn = range(n)
        E = {x for x in rn if op[x][x] == x}
        assert len([e for e in E if all(op[e][x] == x == op[x][e] for x in rn)]) == 1, "not a monoid"

        # If Se = Sf then there's no need to try using both Se and Sf a projective modules
        # so only included modules with that one.
        Lclass_to_e = {}
        for e in sorted(E):
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
        self.extend(up_to_dimension, verbose=verbose)
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
        # Use local imports so the rest can be run in vanilla Python without sympy
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

    def extend(self, up_to_dimension, verbose=False):
        """Compute modules and maps up to the module in dimension up_to_dimension"""
        while len(self.module_list) - 1 < up_to_dimension:
            self.extend_once(verbose=verbose)

    def extend_once(self, verbose=False):
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
        kernel_basis = get_kernel_basis(Z_matrix, width, verbose=verbose)
        del Z_matrix
        if len(kernel_basis) < 100:
            input_gens, right_mul_matrix = self.cover(last_gens, kernel_basis, verbose=verbose)
        else:
            input_gens, right_mul_matrix = self.cover_fast(last_gens, kernel_basis, verbose=verbose)
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

    def cover_fast(self, output_gens, kernel_basis, verbose=False):
        """
        Given a list `output_gens` of idempotents (e1, ..., en)
        and a list `kernel_basis` of vectors in

            X := ZZ[S]e1 (+) ... (+) ZZ[S]en,

        produce a new module

            Y := ZZ[S]f1 (+) ... (+) ZZ[S]fm

        and a ZZ[S]-linear map d: X --> Y
        such that d(X) = the ZZ-span of `kernel_basis`.

        This has the same API as cover(), but does no try very hard
        to make X as small as possible. In pseudo-code, cover_fast()
        just does:

            for k in kernel_basis:
                if k is not already covered by d(X):
                    add a summand ZZ[S]f with map a right-multiplication by k,
                    satisfying ZZ[S]fk = ZZ[S]k
        """
        if len(kernel_basis) == 0:
            input_gens = []
            right_mul_matrix = [[] for _ in range(len(output_gens))]
            return input_gens, right_mul_matrix

        # Correspondence between the ZZ-basis for X
        # and the direct summands of X
        output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(self.e_to_Lclass[gen]))]
        output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
        N = len(output_index_pairs)

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
        covered = FreeAbelianSubmodule(N)

        if verbose and len(kernel_basis) > 100:
            from tqdm import tqdm
            kernel_basis = tqdm(kernel_basis, desc=f"dim{len(self.module_list)}", dynamic_ncols=True, smoothing=0.0, ascii=True, miniters=0)

        for vec in kernel_basis:
            if vec not in covered:
                e = None
                for s in range(len(self.op)):
                    svec = left_multiply_vector(s, vec)
                    covered.add(svec)
                    if s in self.e_to_Lclass and svec == vec:
                        if e is None or len(self.e_to_Lclass[s]) < len(self.e_to_Lclass[e]):
                            e = s
                assert e is not None, "Not a monoid?"
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

    def cover(self, output_gens, kernel_basis, verbose=False):
        """
        Given a list `output_gens` of idempotents (e1, ..., en)
        and a list `kernel_basis` of vectors in

            X := ZZ[S]e1 (+) ... (+) ZZ[S]en,

        produce a new module

            Y := ZZ[S]f1 (+) ... (+) ZZ[S]fm

        and a ZZ[S]-linear map d: X --> Y
        such that d(X) = the ZZ-span of `kernel_basis`.

        This has the same API as cover(), but does no try very hard
        to make X as small as possible. In pseudo-code, cover_fast()
        just does:

        This has the same API as cover_fast(), but tries harder
        to make a small module X.
        At each step, cover() finds which vector will pay off most to add,
        and then we add it, along with any other vectors
        that are expected to pay off similar amounts.
        """
        if len(kernel_basis) == 0:
            input_gens = []
            right_mul_matrix = [[] for _ in range(len(output_gens))]
            return input_gens, right_mul_matrix

        output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(self.e_to_Lclass[gen]))]
        output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
        N = len(output_index_pairs)

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

        if verbose:
            print("making table...")
        left_multiply_index_table = [
            [left_multiply_index(s, index) for index in range(N)]
            for s in range(len(self.op))
        ]

        def left_multiply_vector(s, vec):
            result = [0] * len(vec)
            for out_index, x in zip(left_multiply_index_table[s], vec):
                result[out_index] += x
            return result

        if verbose:
            print("finding ZS spans...")
        ZS_spans = []
        for vec in kernel_basis:
            sub = FreeAbelianSubmodule(N)
            for s in range(len(self.op)):
                sub.add(left_multiply_vector(s, vec))
            ZS_spans.append(sub)

        idempotents_by_size = sorted(self.e_to_Lclass.keys(), key=lambda e: len(self.e_to_Lclass[e]))

        if verbose:
            print("finding idempotents...")
        kindex_to_e = []
        for vec in kernel_basis:
            best_e = None
            for e in idempotents_by_size:
                if left_multiply_vector(e, vec) == vec:
                    best_e = e
                    break
            assert best_e is not None
            kindex_to_e.append(best_e)

        if verbose:
            print("computing base inclusions...")
        base_inclusions = []
        for kindex1 in range(len(kernel_basis)):
            span = ZS_spans[kindex1]
            included = {kindex2 for kindex2, k in enumerate(kernel_basis)
                        if kindex2 == kindex1 or k in span}
            base_inclusions.append(included)

        kindexes_in_covering_order = sorted(
            range(len(kernel_basis)),
            key = lambda kindex: len(base_inclusions[kindex]),
            reverse=True
        )

        already_covered_kindexes = set()
        already_covered = FreeAbelianSubmodule(N)
        input_gens = []
        right_mul_columns = []

        def add_summand(kindex):
            already_covered_kindexes.update(inclusions[kindex])
            nonlocal already_covered
            already_covered += ZS_spans[kindex]
            right_mul_column = [[] for _ in output_gens]
            for index, coeff in enumerate(kernel_basis[kindex]):
                if coeff:
                    i, ii = output_index_pairs[index]
                    Lclass = self.e_to_Lclass[output_gens[i]]
                    m = Lclass[ii]
                    right_mul_column[i].append((coeff, m))
            input_gens.append(kindex_to_e[kindex])
            right_mul_columns.append(right_mul_column)

        while True:
            if verbose:
                print(f"{len(kernel_basis)-len(already_covered_kindexes)} remaining")
            inclusions = {kindex: base_inclusions[kindex] | already_covered_kindexes
                          for kindex in kindexes_in_covering_order
                          if kindex not in already_covered_kindexes}
            for kindex, to_be_included in inclusions.items():
                in_question = [kindex2 for kindex2 in range(len(kernel_basis)) if kindex2 not in to_be_included]
                if not in_question:
                    continue
                new_span = already_covered + ZS_spans[kindex]
                for kindex2 in in_question:
                    if kernel_basis[kindex2] in new_span:
                        to_be_included.add(kindex2)
            total_found = sum(
                len(to_be_included - already_covered_kindexes - base_inclusions[kindex])
                for kindex, to_be_included in inclusions.items()
            )

            kindex = max(
                inclusions.keys(),
                key=lambda kindex: len(inclusions[kindex]) / len(self.e_to_Lclass[kindex_to_e[kindex]])
            )
            num_added = len(self.e_to_Lclass[kindex_to_e[kindex]])
            num_covered = len(inclusions[kindex]) - len(already_covered_kindexes)
            efficiency = num_covered / num_added - 0.0001
            if verbose:
                print(f"found {total_found} new inclusions --> {efficiency=}")

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
                if kindex in already_covered_kindexes:
                    continue
                num_covered_approx = len(to_be_included - already_covered_kindexes)
                num_added = len(self.e_to_Lclass[kindex_to_e[kindex]])
                if num_covered_approx / num_added >= efficiency:
                    add_summand(kindex)

            # Get already_covered_kindexes all the way up to date before starting again.
            for kindex in range(len(kernel_basis)):
                if kindex not in already_covered_kindexes:
                    if kernel_basis[kindex] in already_covered:
                        already_covered_kindexes.add(kindex)

            if len(already_covered_kindexes) == len(kernel_basis):
                # covered everything!
                break

        del ZS_spans
        del already_covered

        if verbose:
            print("transposing...")
        assert len(right_mul_columns) == len(input_gens)
        for col in right_mul_columns:
            assert len(col) == len(output_gens)
        right_mul_matrix = [
            [right_mul_columns[j][i] for j in range(len(input_gens))]
            for i in range(len(output_gens))
        ]
        assert len(right_mul_matrix) == len(output_gens)

        if verbose:
            print(f"done with dim{len(self.module_list)}")
        return input_gens, right_mul_matrix


def find_good_resolution(op0, peek_dim=4, verbose=False):
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
            res.extend_once(verbose=verbose)
            if len(res.module_list[-1]) == 0:
                if verbose:
                    print("short circuit: finite resolution!")
                return res
    print([len(res.module_list[-1]) for res in resolutions])
    return min(resolutions, key=lambda res: len(res.module_list[-1]))
