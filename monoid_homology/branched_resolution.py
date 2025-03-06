from collections import defaultdict
from bisect import bisect, bisect_left
from abelian_groups import FinitelyGeneratedAbelianGroup
import itertools
from functools import cache
from operator import itemgetter
ig0 = itemgetter(0)
try:
    from sage.all import Matrix, ZZ, ChainComplex
    from sage.all import xgcd as sage_xgcd
    from sage.misc.verbose import set_verbose
    from tqdm import tqdm
    ZZ0 = ZZ(0)
except ImportError:
    pass

# def xgcd(a, b):
#     # Maintain the invariants:
#     #          x * a +      y * b ==      g
#     #     next_x * a + next_y * b == next_g
#     # Do the Euclidean algorithm to (g, next_g),
#     # but carry the rest of the equations along for the ride.
#     x, next_x = 1, 0
#     y, next_y = 0, 1
#     g, next_g = a, b
#     while next_g:
#         q = g // next_g
#         x, next_x = next_x, x - q * next_x
#         y, next_y = next_y, y - q * next_y
#         g, next_g = next_g, g - q * next_g
#     if g < 0:
#         x, y, g = -x, -y, -g
#     return x, y, g

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
            D[i1], D[i2] = D[i2], D[i1]
            # Di1[:], Di2[:] = Di2[:], Di1[:]
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
            for jj in range(j, n):
                Di1[jj] += q*Di2[jj]
            D[i1], D[i2] = D[i2], D[i1]
            # Di1[:], Di2[:] = Di2[:], Di1[:]
            # for jj in range(j, n):
            #     Di2[jj] += q*Di1[jj]
            assert D[i1][j] == b
            assert D[i2][j] == 0
        else:
            g, x, y = sage_xgcd(a, b)
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
            g, x, y = map(int, sage_xgcd(a, b))
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

    def first_pass(k):
        none_in_rest_of_col = not any(True for i in range(k+1, m) if D[i][k])
        none_in_rest_of_row = not any(True for j in range(k+1, n) if D[k][j])
        if abs(D[k][k]) == 1 and (none_in_rest_of_row or none_in_rest_of_col):
            return
        if none_in_rest_of_row and none_in_rest_of_col:
            return

        # Try to get a 1 in the pivot position as fast as possible.
        col_sums = [sum(abs(D[i][j]).bit_length() for i in range(k, m)) for j in range(k, n)]
        row_sums = [sum(abs(D[i][j]).bit_length() for j in range(k, n)) for i in range(k, m)]

        best_i, best_j = k, k
        best_is_zero = (D[k][k] == 0)
        best_abs = abs(D[k][k])
        best_sum = col_sums[0] + row_sums[0]

        for i in range(k, m):
            row_sum = row_sums[i-k]
            for j in range(k, n):
                Dij = D[i][j]
                this_is_zero = (Dij == 0)
                if not (this_is_zero <= best_is_zero):
                    continue
                this_abs = abs(Dij)
                if this_is_zero == best_is_zero and not (this_abs <= best_abs):
                    continue
                this_sum = col_sums[j-k] + row_sum
                if this_is_zero == best_is_zero and this_abs == best_abs and not (this_sum <= best_sum):
                    continue
                best_i, best_j = i, j
                best_is_zero = this_is_zero
                best_abs = this_abs
                best_sum = this_sum
                # if (best_is_zero, best_abs, best_sum) == (False, 1, 2):
                #     break
                if not best_is_zero and best_sum == 2 * best_abs.bit_length():
                    break
            else:
                # j loop completed --> next i loop
                continue
            # j loop had break --> break i loop
            break

        i, j = best_i, best_j
        # i, j = min(((i, j) for i in range(k, m) for j in range(k, n)), key=keyfunc)

        assert best_abs == abs(D[i][j]), (best_abs, D[i][j])

        D[k], D[i] = D[i], D[k]
        if j > k:
            improve_with_col_ops(k, j, k)

        assert abs(D[k][k]) == 0 or best_abs % abs(D[k][k]) == 0, (best_abs, D[k][k])

        if verbose:
            if best_abs != 1 or best_sum >= 50:
                print(f"{abs(D[k][k])=}, {col_sums[j-k]=}, {row_sums[i-k]=}")

    def isolate_loners():

        for i in range(m):
            try:
                [j] = (j for j in range(n) if D[i][j])
            except ValueError:
                continue
            q = abs(D[i][j])
            for ii in range(m):
                if ii != i:
                    D[ii][j] %= q

        # Initially isolate everything that lives in the its own row and column
        row_counts = [sum(1 for j in range(n) if D[i][j]) for i in range(m)]
        col_counts = [sum(1 for i in range(m) if D[i][j]) for j in range(n)]
        loners = []
        i_used = set()
        j_used = set()
        for i, row in enumerate(D):
            for j, val in enumerate(row):
                if val == 0 or i in i_used or j in j_used:
                    continue
                if abs(val) == 1 and (row_counts[i] == 1
                                    #   or col_counts[j] == 1
                                      ):
                    loners.append((i, j))
                    i_used.add(i)
                    j_used.add(j)
                elif row_counts[i] == 1 and col_counts[j] == 1:
                    loners.append((i, j))
                    i_used.add(i)
                    j_used.add(j)

        loners.sort()
        assert len({i for i, j in loners}) == len({j for i, j in loners}) == len(loners)

        location_of_column = list(range(n))

        for dest, (i, j0) in enumerate(loners):
            j = location_of_column[j0]
            assert dest <= i
            if dest < i:
                D[dest], D[i] = D[i], D[dest]
            if dest != j:
                location_of_column[j], location_of_column[dest] = location_of_column[dest], location_of_column[j]
                # Unconditionally swap the columns
                for Dii in D:
                    Dii[dest], Dii[j] = Dii[j], Dii[dest]
                for Tii in T:
                    Tii[dest], Tii[j] = Tii[j], Tii[dest]
        if verbose:
            print(f"started with {len(loners)} loners out of {min(m, n)}")

    isolate_loners()

    if verbose:
        range_mn = tqdm(
            range(min(m,n)),
            desc=f"SNF",
            dynamic_ncols=True,
            smoothing=0.05,
            ascii=True,
            miniters=0,
            total=min(m, n)
        )
    else:
        range_mn = range(min(m,n))

    # make diagonal
    for k in range_mn:
        if all(D[k][j] == 0 for j in range(k+1, n)):
            q = D[k][k]
            if q:
                for i in range(k+1, m):
                    D[i][k] %= q
        # else:
        #     first_pass(k)


        while True:
            for i in range(k+1, m):
                improve_with_row_ops(k, i, k)
            if all(D[k][j] == 0 for j in range(k+1, n)):
                break
            for j in range(k+1, n):
                improve_with_col_ops(k, j, k)
            if all(D[i][k] == 0 for i in range(k+1, m)):
                break
            q = D[k][k]
            if q:
                for i in range(k+1, m):
                    D[i][k] %= q

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

    if 0:
        size = num_cols * len(A)
        if size < 200_000:
        # if 1:
            M = Matrix(ZZ, len(A), num_cols, A, sparse=False)
            if verbose:
                print(f"kernel of {len(A)}x{num_cols}={len(A)*num_cols:,} matrix...")
                # set_verbose(2)
            K = M.right_kernel_matrix(
                # algorithm="default",
                algorithm="padic",
                # algorithm="pari",
                # basis="computed",
                # basis="echelon",
                basis="LLL",
                verbose=verbose,
            )
            result = [list(map(int, row)) for row in K]
            if verbose:
                print(f"{len(A)}x{num_cols} matrix has nullity {K.nrows()}.")
                # set_verbose(0)
            # result.sort(key=vec_sort_key)
            return result

    m = len(A)
    n = num_cols
    D, T = partial_smithify(A, n, verbose=verbose)
    ker_D_indices = [j for j in range(n) if j >= m or D[j][j] == 0]
    columns = [
        [T[i][j] for i in range(n)]
        for j in ker_D_indices
    ]
    # columns.sort(key=vec_sort_key)

    # size = max(
    #     (max(map(int.bit_length, map(abs, col)), default=0) for col in columns),
    #     default=0
    # )

    # if size <= min(n, len(columns))*4:
    # if 1:
    # verbose=True
    if 0:
    # if size <= 8:
        if verbose:
            print(f"echelonizing {len(columns)}x{num_cols}...")
        gen = FreeAbelianSubmodule(n)
        it = columns
        if verbose:
            it = tqdm(
                it,
                desc=f"ech",
                dynamic_ncols=True,
                smoothing=0.05,
                ascii=True,
                miniters=0,
                total=len(columns)
            )
        for col in it:
            gen.add(col)
        assert len(gen.basis) == len(columns)
        columns = gen.basis
        if verbose:
            print("done")
    # elif VERBOSE:
    else:
        if verbose:
            print(f"don't echelonize {len(columns)}x{num_cols}")

    return columns

def union_find(n, pairs):
    parent = list(range(n))
    size = [1] * n
    for x, y in pairs:
        while parent[x] != x:
            x, parent[x] = parent[x], parent[parent[x]]
        while parent[y] != y:
            y, parent[y] = parent[y], parent[parent[y]]
        if x == y:
            continue
        if size[x] < size[y]:
            x, y = y, x
        parent[y] = x
        size[x] += size[y]
    root_to_children = defaultdict(list)
    for x0 in range(n):
        x = x0
        while parent[x] != x:
            x, parent[x] = parent[x], parent[parent[x]]
        root_to_children[x].append(x0)
    bins = list(root_to_children.values())
    return bins


class FreeAbelianSubmodule:
    """
    A submodule of ZZ^n, with a basis stored as row-vectors in row echelon form.

    Mutable, so we can relatively quickly add in the spans of new vectors.
    """
    __slots__ = ["N",
                 "basis",
                 "pivot_location_in_column",
                 "pivot_location_in_row",
                 "zero_columns",
                 "depth",
                 "depth_for_next_HNFify"]

    def __init__(self, ambient_dimension):
        self.N = N = ambient_dimension
        self.pivot_location_in_column = [None] * N
        self.pivot_location_in_row = []
        self.basis = []
        self.zero_columns = list(range(N))
        # self.depth = ZZ0
        # self.depth_for_next_HNFify = 1000

    def copy(self):
        new = object.__new__(type(self))
        new.N = self.N
        new.basis = list(map(list.copy, self.basis))
        new.pivot_location_in_column = self.pivot_location_in_column.copy()
        new.pivot_location_in_row = self.pivot_location_in_row.copy()
        new.zero_columns = self.zero_columns.copy()
        # new.depth = self.depth
        # new.depth_for_next_HNFify = self.depth_for_next_HNFify
        return new

    def assert_consistent(self):
        """assert we're in in row echelon form"""
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
    
    # def HNFify(self):
        # print(f"\r\nuh oh: depth={self.depth:,}\r\n")
        # self.depth_for_next_HNFify *= 2
        # print(f"\nHNFifying at depth {self.depth}...")
        # M = Matrix(len(self.basis), self.N, self.basis)
        # old_depth = self.depth
        # self.pivot_location_in_column = [None] * self.N
        # self.pivot_location_in_row = []
        # self.basis = []
        # self.zero_columns = list(range(self.N))
        # # set_verbose(2)
        # # H = M.LLL()
        # # H = M.hermite_form()
        # # set_verbose(0)
        # assert M.nrows() == H.nrows()
        # assert M.ncols() == H.ncols()
        # print(f"got LLL")
        # for row in H:
        #     self.add(list(map(int, row)), maybe_HNFify=False)
        # print(f"got depth {self.depth}")
        # self.depth_for_next_HNFify = old_depth * 2

    def __contains__(self, vec):
        """Does this subspace contain this vector?"""
        for _ in filter(vec.__getitem__, self.zero_columns):
            return False
        col_piv = self.pivot_location_in_column
        N = self.N
        basis = self.basis
        # vec = list(map(ZZ, vec))
        vec = vec.copy()
        for j in filter(vec.__getitem__, range(N)):
            p = col_piv[j]
            if p is None:
                # can't zero this vec entry out
                # without disrupting previous parts
                return False
            a = basis[p][j]
            b = vec[j]
            if b % a:
                # This pivot can't zero this entry
                return False
            else:
                q = b // a
                row = basis[p]
                for jj in range(j, N):
                    vec[jj] -= q * row[jj]
        return True

    def add(self, vec0, maybe_HNFify=True):
        col_piv = self.pivot_location_in_column
        row_piv = self.pivot_location_in_row
        N = self.N
        basis = self.basis
        assert len(vec0) == N
        # vec = list(map(ZZ, vec0))
        vec = vec0.copy()
        for j in filter(vec.__getitem__, range(N)):
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

                zc = self.zero_columns
                s = bisect_left(zc, j)
                zc[s:] = itertools.filterfalse(vec0.__getitem__, zc[s:])

                # self.depth = max(self.depth,
                #                  max(map(abs, vec[j:]), default=ZZ0).nbits())
                # if maybe_HNFify and self.depth >= self.depth_for_next_HNFify:
                #     self.HNFify()
                # self.assert_consistent()
                return
            row = basis[p]
            a = row[j]
            b = vec[j]
            # assert a != 0
            # assert b != 0
            if not b % a:
                q = b // a
                for jj in filter(row.__getitem__, range(j, N)):
                    vec[jj] -= q * row[jj]
            elif not a % b:
                row[j:], vec[j:] = vec[j:], row[j:]
                q = a // b
                for jj in filter(row.__getitem__, range(j, N)):
                    vec[jj] -= q * row[jj]
                # self.depth = max(self.depth,
                #                  max(map(abs, vec[j:]), default=ZZ0).nbits(),
                #                  max(map(abs, row[j:]), default=ZZ0).nbits())
            else:
                g, x, y = sage_xgcd(a, b)
                ag = a//g
                mbg = -b//g
                for jj in range(j, N):
                    aa = ZZ(row[jj])
                    bb = ZZ(vec[jj])
                    row[jj] = x*aa + y*bb
                    vec[jj] = mbg*aa + ag*bb
                # self.depth = max(self.depth,
                #                  max(map(abs, vec[j:]), default=ZZ0).nbits(),
                #                  max(map(abs, row[j:]), default=ZZ0).nbits())
            # assert vec[j] == 0
        # making it to the end means that vec has been zeroed out.
        # nothing more needs to be done.
        # assert not any(vec)
        # self.assert_consistent()

    def get_coefficients(self, vec0):
        vec = vec0
        col_piv = self.pivot_location_in_column
        N = self.N
        basis = self.basis
        coefficients = [0] * len(self.basis)
        for j in range(N):
            if vec[j]:
                p = col_piv[j]
                if p is None:
                    # can't zero this vec entry out
                    # without disrupting previous parts
                    raise ValueError("vector not in subspace")
                a = basis[p][j]
                b = vec[j]
                if b % a != 0:
                    # This pivot can't zero this entry
                    raise ValueError("vector not in subspace")
                else:
                    if vec is vec0:
                        # copy on write
                        vec = vec.copy()
                    q = b // a
                    coefficients[j] = q
                    row = basis[p]
                    # assert set(vec[:j]) <= {0}
                    for jj in range(j, N):
                        vec[jj] -= q * row[jj]
        return coefficients

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


MAX_SIZE_FOR_GREEDIER_COVERING = 300
MAX_SIZE_FOR_COVERING_IMPROVEMENT = 300

def get_cover_by_mapping(output_idempotents, submodule_Zbasis, op, e_to_Se, verbose=False, desc='cover'):
    """
    Given a list of idempotents (e1, .., en) of S
    and a list of vectors (represented as lists of integers) spanning
    a ZS-submodule of

        Y := ZSe1 (+) ... (+) ZSen,

    produce a new module

        X := ZSf1 (+) ... (+) ZSfm

    and a ZS-linear map d: X --> Y such that d(X) = the Z-span of A.
    This map will be represented as a matrix of elements of ZS
    to serve a right multipliers. An individual element
    of ZS will be a list of pairs (coeff, m),
    where coeff is an integer and m is in S.
    """
    if len(submodule_Zbasis) == 0:
        return [], [[] for _ in output_idempotents]

    # "i" represents a choice of output idempotent e
    # "ii" represents a choice of element within Se.
    # "index" represents the accumulated index of an element across all idempotents
    # Represent here the bijection (i, ii) <---> index
    output_index_pairs = [(i, ii) for i, e in enumerate(output_idempotents)
                          for ii in range(len(e_to_Se[e]))]
    output_index_pair_to_index = {pair: index for index, pair in enumerate(output_index_pairs)}
    N = len(output_index_pairs)
    assert len(submodule_Zbasis[0]) == N

    # Utilities for dealing with the action of S on vectors of the submodule
    # here "kindex" will refer to an index into submodule_Zbasis
    def left_multiply_index_pair(s, i, ii):
        e = output_idempotents[i]
        Se = e_to_Se[e]
        x = Se[ii]
        sx = op[s][x]
        return i, Se.index(sx)
    @cache
    def left_multiply_index(s, index):
        (i, ii) = output_index_pairs[index]
        (i, ii) = left_multiply_index_pair(s, i, ii)
        return output_index_pair_to_index[i, ii]
    def left_multiply_vector(s, vec):
        result = [0] * len(vec)
        for index in filter(vec.__getitem__, range(len(vec))):
            result[left_multiply_index(s, index)] += vec[index]
        return result
    @cache
    def left_multiply_vector_from_kindex(s, kindex):
        return left_multiply_vector(s, submodule_Zbasis[kindex])
    @cache
    def get_span_from_kindex(kindex):
        # Pre-compute the span s*vec to consolidate these correlated
        # vectors {s*vec : s in S} before reintroducing them to any others.
        span = FreeAbelianSubmodule(N)
        for s in range(len(op)):
            svec = left_multiply_vector_from_kindex(s, kindex)
            span.add(svec)
        return span

    # Find idempotent e such that e*vec == vec
    @cache
    def get_idempotent_for_kindex(kindex):
        vec = submodule_Zbasis[kindex]
        e_options = [e for e in e_to_Se.keys()
                     if left_multiply_vector_from_kindex(e, kindex) == vec]
        return min(e_options, key=lambda e: len(e_to_Se[e]))

    solution_kindexes = []

    def do_cover_simple():
        # Simpler algorithm: just add the vector if we don't have it yet.
        it = submodule_Zbasis
        if verbose:
            it = tqdm(it, desc=desc, dynamic_ncols=True, smoothing=0.05, ascii=True, miniters=1)
        covered = FreeAbelianSubmodule(N)
        for kindex, vec in enumerate(it):
            if vec not in covered:
                solution_kindexes.append(kindex)
                covered += get_span_from_kindex(kindex)
        del it, covered
    
    def do_cover_greedy():
        # More complicated, slower algorithm: try to add the most optimal vector at each step.
        if verbose:
            pbar = tqdm(total=len(submodule_Zbasis), desc=desc)
        covered = FreeAbelianSubmodule(N)
        covered_kindexes = set()
        implications = set() # (a, b) in this set means including vector a would also cover vector b
        while len(covered_kindexes) < len(submodule_Zbasis):
            kindex_choice_to_hypothetical_span = {}
            kindex_choice_to_others_covered = {}
            for kindex_choice in range(len(submodule_Zbasis)):
                if kindex_choice in covered_kindexes:
                    continue
                hypothetical_span = covered.copy()
                hypothetical_span += get_span_from_kindex(kindex_choice)
                kindex_choice_to_hypothetical_span[kindex_choice] = hypothetical_span
                would_be_covered_kindexes = {
                    kindex2
                    for kindex2 in range(len(submodule_Zbasis))
                    if kindex2 not in covered_kindexes
                    and (
                        (kindex_choice, kindex2) in implications
                        or
                        submodule_Zbasis[kindex2] in hypothetical_span
                    )
                }
                for kindex2 in would_be_covered_kindexes:
                    implications.add((kindex_choice, kindex2))
                kindex_choice_to_others_covered[kindex_choice] = would_be_covered_kindexes
            def efficiency(kindex_choice):
                others = len(kindex_choice_to_others_covered[kindex_choice])
                cost = len(e_to_Se[get_idempotent_for_kindex(kindex_choice)])
                return others / cost + 0.001 * others
            best_kindex = max(kindex_choice_to_others_covered.keys(), key=efficiency)
            solution_kindexes.append(best_kindex)
            covered = kindex_choice_to_hypothetical_span[best_kindex]
            for kindex2 in kindex_choice_to_others_covered[best_kindex]:
                if kindex2 not in covered_kindexes:
                    covered_kindexes.add(kindex2)
                    if verbose:
                        pbar.update(1)
        if verbose:
            pbar.close()

    # Choose between two algorithms based on the size of the submodule.
    if len(submodule_Zbasis) > MAX_SIZE_FOR_GREEDIER_COVERING:
        do_cover_simple()
    else:
        do_cover_greedy()

    # Now everything should be covered. Optionally try to improve on this.
    def shrink_solution():
        if verbose:
            pbar = tqdm(total=len(solution_kindexes) * 2,
                        desc=desc+"shrink", smoothing=0.05, miniters=1)
        # suffix_subspans[k] is the sum of the last k spans
        suffix_subspans = [FreeAbelianSubmodule(N)]
        for kindex in reversed(solution_kindexes):
            suffix_subspans.append(suffix_subspans[-1] + get_span_from_kindex(kindex))
            if verbose:
                pbar.update(1)
        prefix_subspan = FreeAbelianSubmodule(N)
        new_solution_kindexes = []
        for kindex_index, kindex in enumerate(solution_kindexes):
            vec = submodule_Zbasis[kindex]
            suffix_subspan = suffix_subspans[len(solution_kindexes) - kindex_index - 1]
            zero_columns = set(suffix_subspan.zero_columns) & set(prefix_subspan.zero_columns)
            if any(vec[j] for j in zero_columns):
                redundant = False
            else:
                redundant = (
                    vec in prefix_subspan
                    or vec in suffix_subspan
                    or vec in (prefix_subspan + suffix_subspan)
                )
            if verbose:
                pbar.update(1)
            if not redundant:
                new_solution_kindexes.append(kindex)
                prefix_subspan += get_span_from_kindex(kindex)
        if verbose:
            pbar.close()
            print(f"Reduced {len(solution_kindexes)} --> {len(new_solution_kindexes)}")
        return new_solution_kindexes

    if len(solution_kindexes) <= MAX_SIZE_FOR_COVERING_IMPROVEMENT:
        solution_kindexes = shrink_solution()

    # Output the solution
    input_idempotents = list(map(get_idempotent_for_kindex, solution_kindexes))
    right_mul_columns = []
    for kindex in solution_kindexes:
        column = [[] for _ in output_idempotents]
        vec = submodule_Zbasis[kindex]
        for (i, ii), coeff in zip(output_index_pairs, vec):
            if coeff:
                e = output_idempotents[i]
                Se = e_to_Se[e]
                m = Se[ii]
                column[i].append((coeff, m))
        right_mul_columns.append(column)
    right_mul_matrix = [
        [right_mul_columns[j][i] for j in range(len(input_idempotents))]
        for i in range(len(output_idempotents))
    ]
    return input_idempotents, right_mul_matrix

# def cover_fast(output_gens, kernel_basis, op, e_to_Lclass, verbose=False, desc='cover'):
#     """
#     Given a list `output_gens` of idempotents (e1, ..., en)
#     and a list `kernel_basis` of vectors in

#         Y := ZZ[S]e1 (+) ... (+) ZZ[S]en,

#     produce a new module

#         X := ZZ[S]f1 (+) ... (+) ZZ[S]fm

#     and a ZZ[S]-linear map d: X --> Y
#     such that d(X) = the ZZ-span of `kernel_basis`.

#     This has the same API as cover(), but does not try very hard
#     to make X as small as possible. In pseudo-code, cover_fast()
#     just does:

#         for k in kernel_basis:
#             if k is not already covered by d(X):
#                 add a summand ZZ[S]f with map a right-multiplication by k,
#                 satisfying ZZ[S]fk = ZZ[S]k
#     """
#     if len(kernel_basis) == 0:
#         input_gens = []
#         right_mul_matrix = [[] for _ in range(len(output_gens))]
#         return input_gens, right_mul_matrix

#     # Correspondence between the ZZ-basis for X
#     # and the direct summands of X
#     output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(e_to_Lclass[gen]))]
#     output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
#     N = len(output_index_pairs)

#     def left_multiply_index(s, index):
#         # Takes a one-hot Z-basis vector at index
#         # and multiplies it on the left by the semigroup element s
#         # to find the index of the result one-hot Z-basis vector
#         (i, ii) = output_index_pairs[index]
#         Lclass = e_to_Lclass[output_gens[i]]
#         x = Lclass[ii]
#         sx = op[s][x]
#         ii_new = Lclass.index(sx)
#         return output_index_pair_to_index[i, ii_new]
#     left_multiply_index_table = [
#         [left_multiply_index(s, index) for index in range(N)]
#         for s in range(len(op))
#     ]

#     def left_multiply_vector(s, vec):
#         result = [0] * len(vec)
#         table_s = left_multiply_index_table[s]
#         for i in filter(vec.__getitem__, range(N)):
#             result[table_s[i]] += vec[i]
#         return result

#     input_gens = []
#     right_mul_columns = []
#     covered = FreeAbelianSubmodule(N)

#     if verbose and len(kernel_basis) > 100:
#         kernel_basis = tqdm(kernel_basis,
#                             desc=desc,
#                             # desc=f"dim{len(self.module_list)}",
#                             dynamic_ncols=True,
#                             smoothing=0.05,
#                             ascii=True,
#                             miniters=1)

#     for vec in kernel_basis:
#         if covered.depth > 100_000:
#             e_choices = [e for e in e_to_Lclass if left_multiply_vector(e, vec) == vec]
#             e = min(e_choices, key=lambda e: len(e_to_Lclass[e]))
#             input_gens.append(e)
#             right_mul_column = [[] for _ in output_gens]
#             for index, coeff in enumerate(vec):
#                 if coeff:
#                     i, ii = output_index_pairs[index]
#                     Lclass = e_to_Lclass[output_gens[i]]
#                     m = Lclass[ii]
#                     right_mul_column[i].append((coeff, m))
#             right_mul_columns.append(right_mul_column)
#             continue
#         if vec not in covered:
#             span = FreeAbelianSubmodule(N)
#             e_choices = []
#             for s in range(len(op)):
#                 svec = left_multiply_vector(s, vec)
#                 span.add(svec)
#                 if s in e_to_Lclass and svec == vec:
#                     e_choices.append(s)
#             for svec in span.basis:
#                 covered.add(svec)
#             e = min(e_choices, key=lambda e: len(e_to_Lclass[e]))
#             input_gens.append(e)
#             right_mul_column = [[] for _ in output_gens]
#             for index, coeff in enumerate(vec):
#                 if coeff:
#                     i, ii = output_index_pairs[index]
#                     Lclass = e_to_Lclass[output_gens[i]]
#                     m = Lclass[ii]
#                     right_mul_column[i].append((coeff, m))
#             right_mul_columns.append(right_mul_column)
#     del covered

#     assert len(right_mul_columns) == len(input_gens)
#     for col in right_mul_columns:
#         assert len(col) == len(output_gens)
#     right_mul_matrix = [
#         [right_mul_columns[j][i] for j in range(len(input_gens))]
#         for i in range(len(output_gens))
#     ]
#     assert len(right_mul_matrix) == len(output_gens)

#     return input_gens, right_mul_matrix

# def cover(output_gens, kernel_basis, op, e_to_Lclass, verbose=False, desc=''):
#     """
#     Given a list `output_gens` of idempotents (e1, ..., en)
#     and a list `kernel_basis` of vectors in

#         X := ZZ[S]e1 (+) ... (+) ZZ[S]en,

#     produce a new module

#         Y := ZZ[S]f1 (+) ... (+) ZZ[S]fm

#     and a ZZ[S]-linear map d: X --> Y
#     such that d(X) = the ZZ-span of `kernel_basis`.

#     This has the same API as cover_fast(), but tries harder
#     to make a small module X.
#     At each step, cover() finds which vector will pay off most to add,
#     and then we add it, along with any other vectors
#     that are expected to pay off similar amounts.
#     """
#     verbose = verbose and len(kernel_basis) > 10
#     if len(kernel_basis) == 0:
#         input_gens = []
#         right_mul_matrix = [[] for _ in range(len(output_gens))]
#         return input_gens, right_mul_matrix

#     output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(e_to_Lclass[gen]))]
#     output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
#     N = len(output_index_pairs)

#     def left_multiply_index(s, index):
#         # Takes a one-hot Z-basis vector at index
#         # and multiplies it on the left by the semigroup element s
#         # to find the index of the result one-hot Z-basis vector
#         (i, ii) = output_index_pairs[index]
#         Lclass = e_to_Lclass[output_gens[i]]
#         x = Lclass[ii]
#         sx = op[s][x]
#         ii_new = Lclass.index(sx)
#         return output_index_pair_to_index[i, ii_new]

#     # if verbose:
#     #     print("making table...")
#     left_multiply_index_table = [
#         [left_multiply_index(s, index) for index in range(N)]
#         for s in range(len(op))
#     ]

#     def left_multiply_vector(s, vec):
#         result = [0] * len(vec)
#         table_s = left_multiply_index_table[s]
#         for i in filter(vec.__getitem__, range(len(vec))):
#             result[table_s[i]] += vec[i]
#         return result

#     # if verbose:
#     #     print("finding ZS spans...")
#     ZS_spans = []
#     for vec in kernel_basis:
#         sub = FreeAbelianSubmodule(N)
#         for s in range(len(op)):
#             sub.add(left_multiply_vector(s, vec))
#         # sub.HNFify()
#         ZS_spans.append(sub)

#     idempotents_by_size = sorted(e_to_Lclass.keys(), key=lambda e: len(e_to_Lclass[e]))

#     # if verbose:
#     #     print("finding idempotents...")
#     kindex_to_e = []
#     for vec in kernel_basis:
#         best_e = None
#         for e in idempotents_by_size:
#             if left_multiply_vector(e, vec) == vec:
#                 best_e = e
#                 break
#         assert best_e is not None
#         kindex_to_e.append(best_e)

#     # if verbose:
#     #     print("computing base inclusions...")
#     base_inclusions = []
#     for kindex1 in range(len(kernel_basis)):
#         span = ZS_spans[kindex1]
#         included = {kindex2 for kindex2, k in enumerate(kernel_basis)
#                     if kindex2 == kindex1 or k in span}
#         base_inclusions.append(included)

#     kindexes_in_covering_order = sorted(
#         range(len(kernel_basis)),
#         key = lambda kindex: len(base_inclusions[kindex]),
#         reverse=True
#     )

#     already_covered_kindexes = set()
#     already_covered = FreeAbelianSubmodule(N)

#     if verbose:
#         pbar = tqdm(total=len(kernel_basis), desc=desc)

#     used_kindexes = []

#     def add_summand(kindex):
#         used_kindexes.append(kindex)
#         for inc in inclusions[kindex]:
#             if inc not in already_covered_kindexes:
#                 already_covered_kindexes.add(inc)
#                 if verbose:
#                     pbar.update(1)
#         # already_covered_kindexes.update(inclusions[kindex])
#         nonlocal already_covered
#         already_covered += ZS_spans[kindex]


#     while True:

#         # if verbose:
#         #     print(f"{len(kernel_basis)-len(already_covered_kindexes)} remaining")
#         inclusions = {kindex: base_inclusions[kindex] | already_covered_kindexes
#                         for kindex in kindexes_in_covering_order
#                         if kindex not in already_covered_kindexes}
#         # already_covered.HNFify()
#         for kindex, to_be_included in inclusions.items():
#             in_question = [kindex2 for kindex2 in range(len(kernel_basis)) if kindex2 not in to_be_included]
#             if not in_question:
#                 continue
#             new_span = already_covered + ZS_spans[kindex]
#             for kindex2 in in_question:
#                 if kernel_basis[kindex2] in new_span:
#                     to_be_included.add(kindex2)
#         total_found = sum(
#             len(to_be_included - already_covered_kindexes - base_inclusions[kindex])
#             for kindex, to_be_included in inclusions.items()
#         )

#         kindex = max(
#             inclusions.keys(),
#             key=lambda kindex: [
#                 len(inclusions[kindex]) / len(e_to_Lclass[kindex_to_e[kindex]]),
#                 # len(inclusions[kindex])
#             ]
#         )
#         num_added = len(e_to_Lclass[kindex_to_e[kindex]])
#         num_covered = len(inclusions[kindex]) - len(already_covered_kindexes)

#         efficiency = num_covered / num_added - 0.0001

#         if verbose:
#             print(f"found {total_found} new inclusions, {efficiency=}")

#         add_summand(kindex)
#         if len(already_covered_kindexes) == len(kernel_basis):
#             # covered everything!
#             break

#         for kindex, to_be_included in inclusions.items():
#             # Attempt at a "lower bound" on num_covered.
#             # Adding this kindex will result in at least `to_be_included`
#             # being covered. The uncertainty is that it could already
#             # have been covered by a previous addition, though then
#             # that previously-added vector's efficiency was greater than expected,
#             # so the average efficiency is still valid.
#             # On the other hand, interacting with the existing cover
#             # means that we could actually cover more, so it's probably a good thing to include.
#             if kindex in already_covered_kindexes:
#                 continue
#             num_covered_approx = len(to_be_included - already_covered_kindexes)
#             num_added = len(e_to_Lclass[kindex_to_e[kindex]])
#             if num_covered_approx / num_added >= efficiency:
#                 add_summand(kindex)

#         # Get already_covered_kindexes all the way up to date before starting again.
#         for kindex in range(len(kernel_basis)):
#             if kindex not in already_covered_kindexes:
#                 if kernel_basis[kindex] in already_covered:
#                     already_covered_kindexes.add(kindex)
#                     if verbose:
#                         pbar.update(1)

#         if len(already_covered_kindexes) == len(kernel_basis):
#             # covered everything!
#             break
#     if verbose:
#         pbar.close()
#     original_size = len(used_kindexes)

#     if 1:
#         suffix_subspans = [FreeAbelianSubmodule(N)]
#         for kindex in reversed(used_kindexes):
#             suffix_subspans.append(suffix_subspans[-1] + ZS_spans[kindex])
#         prefix_subspan = FreeAbelianSubmodule(N)
#         keepers = []
#         it = used_kindexes
#         if len(used_kindexes) > 50:
#             it = tqdm(it, desc=desc+"shrink")
#         for kindex_index, kindex in enumerate(it):
#             vec = kernel_basis[kindex]
#             suffix_subspan = suffix_subspans[len(used_kindexes) - kindex_index - 1]
#             zero_columns = set(suffix_subspan.zero_columns) & set(prefix_subspan.zero_columns)
#             if any(vec[j] for j in zero_columns):
#                 redundant = False
#             else:
#                 redundant = (
#                     vec in prefix_subspan
#                     or vec in suffix_subspan
#                     or vec in (prefix_subspan + suffix_subspan)
#                 )
#             if not redundant:
#                 keepers.append(kindex)
#                 prefix_subspan += ZS_spans[kindex]
#         used_kindexes = keepers

#         if len(used_kindexes) < original_size and original_size > 50:
#             print(f"reduced {original_size} --> {len(used_kindexes)}")

#     # kindex_index = 0
#     # while kindex_index < len(used_kindexes):
#     #     kindex = used_kindexes[kindex_index]
#     #     used_kindexes_copy = used_kindexes[:]
#     #     del used_kindexes_copy[kindex_index]
#     #     assert kindex not in used_kindexes_copy
#     #     other_span = FreeAbelianSubmodule(N)
#     #     for other_kindex in used_kindexes_copy:
#     #         other_span += ZS_spans[other_kindex]
#     #     if verbose:
#     #         pbar.update(1)
#     #     if kernel_basis[kindex] in other_span:
#     #         # redundant
#     #         del used_kindexes[kindex_index]
#     #     else:
#     #         kindex_index += 1

#     del ZS_spans
#     del already_covered

#     # output the solution
#     input_gens = []
#     right_mul_columns = []
#     for kindex in used_kindexes:
#         right_mul_column = [[] for _ in output_gens]
#         for index, coeff in enumerate(kernel_basis[kindex]):
#             if coeff:
#                 i, ii = output_index_pairs[index]
#                 Lclass = e_to_Lclass[output_gens[i]]
#                 m = Lclass[ii]
#                 right_mul_column[i].append((coeff, m))
#         input_gens.append(kindex_to_e[kindex])
#         right_mul_columns.append(right_mul_column)

#     assert len(right_mul_columns) == len(input_gens)
#     for col in right_mul_columns:
#         assert len(col) == len(output_gens)
#     right_mul_matrix = [
#         [right_mul_columns[j][i] for j in range(len(input_gens))]
#         for i in range(len(output_gens))
#     ]
#     assert len(right_mul_matrix) == len(output_gens)

#     # if verbose:
#     #     print(f"done with dim{len(self.module_list)}")
#     return input_gens, right_mul_matrix



class ResolutionNode:
    __slots__ = [

        # Monoid operation: list[list[int]]
        "op",

        # mapping: idempotent e of op --> list of op[...][e]
        "e_to_Lclass",

        # The generators of this module
        "idempotent_list",

        "target_idempotent_list",

        # dict: (index of idempotent, which element of Se) --> Z_basis_index
        "input_index_pair_to_index",
        "output_index_pair_to_index",

        # list: Z_basis_index --> (index of idempotent, which element of Se)
        "input_index_pairs",
        "output_index_pairs",

        # The outgoing map as a list[list[  list[tuple[int,int]]  ]]
        # Where the pairs are (coeff, op_element)
        "outgoing_right_mul_matrix",

        #######################################
        # Data we add later
        #######################################

        # list[list[int]], forgetting the ZS-module structure.
        "Z_matrix",

        # list[list[int]],
        "kernel_Z_basis",

        # each kernel basis element only touches one cell of this partition
        # list[list[int]]
        "partition_of_idempotents", # a.k.a. partition of j-values
        "kindex_to_bindex",
        "partition_of_kindexes",

        # More list[ResolutionNode]
        "children",

        "cached_homology",
        "cached_homology_with_offset",
        "cached_ZG_homology",
    ]

    def __init__(self, op, e_to_Lclass, idempotent_list, target_idempotent_list, outgoing_right_mul_matrix):
        self.op = op
        assert len([e for e in range(len(op))
                    if all(op[e][x] == x == op[x][e]
                           for x in range(len(op))
                           )
                    ]) == 1, "monoid?"
        self.e_to_Lclass = e_to_Lclass
        self.idempotent_list = idempotent_list
        self.target_idempotent_list = target_idempotent_list
        self.outgoing_right_mul_matrix = outgoing_right_mul_matrix

        assert len(outgoing_right_mul_matrix) == len(target_idempotent_list)
        for row in outgoing_right_mul_matrix:
            assert len(row) == len(idempotent_list)
        
        self.input_index_pairs = [(j, jj) for j, gen in enumerate(idempotent_list) for jj in range(len(self.e_to_Lclass[gen]))]
        self.output_index_pairs = [(i, ii) for i, gen in enumerate(target_idempotent_list) for ii in range(len(self.e_to_Lclass[gen]))]
        self.input_index_pair_to_index = {x: i for i, x in enumerate(self.input_index_pairs)}
        self.output_index_pair_to_index = {x: i for i, x in enumerate(self.output_index_pairs)}

        self.Z_matrix = None
        self.kernel_Z_basis = None
        self.partition_of_idempotents = None
        self.kindex_to_bindex = None
        self.partition_of_kindexes = None
        self.children = None
        self.cached_homology = None
        self.cached_homology_with_offset = {}
        self.cached_ZG_homology = None

    def make_Z_matrix(self, verbose=False):
        if verbose:
            print("making Z matrix", flush=True)
        assert self.Z_matrix is None
        matrix = [[0] * len(self.input_index_pairs) for _ in self.output_index_pairs]

        it = self.idempotent_list
        # if verbose:
        #     from tqdm import tqdm
        #     it = tqdm(it, desc=f"Zmat", dynamic_ncols=True, smoothing=0.0, ascii=True, miniters=1)

        for j, x in enumerate(it):
            for i, y in enumerate(self.target_idempotent_list):
                right_mul = self.outgoing_right_mul_matrix[i][j]
                for jj, xx in enumerate(self.e_to_Lclass[x]):
                    input_index = self.input_index_pair_to_index[j,jj]
                    for coeff, m in right_mul:
                        yy = self.op[xx][m]
                        ii = self.e_to_Lclass[y].index(yy)
                        output_index = self.output_index_pair_to_index[i,ii]
                        matrix[output_index][input_index] += coeff

        self.Z_matrix = matrix

    def make_kernel(self, verbose=False):
        assert self.kernel_Z_basis is None
        assert self.Z_matrix is not None
        self.kernel_Z_basis = get_kernel_basis(self.Z_matrix, len(self.input_index_pairs), verbose=verbose)
        self.kernel_Z_basis.sort(key=lambda row: max(map(abs, row)))

    def make_partition(self, verbose=False):
        assert self.kernel_Z_basis is not None
        assert self.partition_of_idempotents is None
        pairs = set()
        for vec in self.kernel_Z_basis:
            summands_touched = set()
            for jindex, val in enumerate(vec):
                if val:
                    j, jj = self.input_index_pairs[jindex]
                    summands_touched.add(j)
            assert summands_touched
            summands_touched = sorted(summands_touched)
            x0 = summands_touched[0]
            for x1 in summands_touched[1:]:
                pairs.add((x0, x1))
        bins = union_find(len(self.idempotent_list), pairs)
        for bin in bins:
            bin.sort()
        bins.sort(key=lambda bin: (len(bin), bin))
        self.partition_of_idempotents = bins
        if verbose and len(bins) > 1:
            print(f"Splitting into {len(bins)} bins...")
 
        assert self.kindex_to_bindex is None
        j_to_bindex = [None] * len(self.idempotent_list)
        for bindex, bin in enumerate(bins):
            for j in bin:
                j_to_bindex[j] = bindex

        kindex_to_bindex = []
        partition_of_kindexes = [[] for _ in bins]
        for kindex, vec in enumerate(self.kernel_Z_basis):
            bindexes_touched = set()
            for jindex, val in enumerate(vec):
                if val:
                    j, jj = self.input_index_pairs[jindex]
                    bindexes_touched.add(j_to_bindex[j])
            [bindex] = bindexes_touched
            kindex_to_bindex.append(bindex)
            partition_of_kindexes[bindex].append(kindex)
        
        if verbose and len(bins) > 1:
            print(f"Done splitting into {len(bins)} bins.")

        self.kindex_to_bindex = kindex_to_bindex
        self.partition_of_kindexes = partition_of_kindexes        

    def make_child(self, bindex, cache=None, verbose=False) -> "ResolutionNode":
        my_idempotent_indexes = self.partition_of_idempotents[bindex]
        my_idempotents = [self.idempotent_list[j] for j in my_idempotent_indexes]
        set_my_idempotent_indexes = set(my_idempotent_indexes)

        my_kernel_vectors = []
        original_kernel_vectors = [self.kernel_Z_basis[kindex]
                                   for kindex in self.partition_of_kindexes[bindex]]
        for vec in original_kernel_vectors:
            subvec = []
            for (j, jj), val in zip(self.input_index_pairs, vec):
                if j in set_my_idempotent_indexes:
                    subvec.append(val)
                else:
                    assert not val
            assert any(subvec)
            my_kernel_vectors.append(subvec)

        # coverfunc = cover if len(my_kernel_vectors) <= 500 else (
        #     cover_fast
        #     # (
        #     # lambda output_gens, kernel_basis, op, e_to_Lclass, verbose=False: (
        #     #     cover_fast(output_gens, kernel_basis, op, e_to_Lclass, verbose=verbose)
        #     # )
        # )
        coverfunc = get_cover_by_mapping
        # coverfunc = cover_fast
        input_gens, incoming_right_mul_matrix = \
            coverfunc(my_idempotents, my_kernel_vectors, self.op, self.e_to_Lclass, verbose=verbose,
                      desc=f"({'abcdefghijklmnopqrstuvwxyz'[id(self)%17]}) child {bindex+1}/{len(self.partition_of_idempotents)}")


        # attempts = []
        # for _ in range(1):
        #     from random import shuffle
        #     # shuffle(my_kernel_vectors)
        #     input_gens, incoming_right_mul_matrix = \
        #         cover(my_idempotents, my_kernel_vectors, self.op, self.e_to_Lclass, verbose=verbose,
        #                 desc=f"({'abcdefghijklmnopqrstuvwxyz'[id(self)%17]}) child {bindex+1}/{len(self.partition_of_idempotents)}")
        #     attempts.append((input_gens, incoming_right_mul_matrix))
        # input_gens, incoming_right_mul_matrix = min(attempts, key=lambda ab: sum(len(self.e_to_Lclass[e]) for e in ab[0]))

        if cache is not None:
            key = (
                tuple(input_gens),
                tuple(my_idempotents),
                tuple(tuple(tuple(entry) for entry in row) for row in incoming_right_mul_matrix),
            )
            cached_child = cache.get(key)
            if cached_child is not None:
                if verbose and input_gens:
                    print("nontrivial cache hit")
                return cached_child
            if verbose:
                print("cache miss")
        
        child = ResolutionNode(self.op, self.e_to_Lclass, input_gens, my_idempotents, incoming_right_mul_matrix)
        if cache is not None:
            if verbose:
                "cache miss"
            cache[key] = child
        return child

    def make_children(self, cache=None, verbose=False):
        if verbose:
            print("making children...")
        assert self.partition_of_idempotents is not None
        children = []
        for bindex in range(len(self.partition_of_idempotents)):
            child = self.make_child(bindex, cache=cache, verbose=verbose)
            children.append(child)
        self.children = children

    def prepare_and_make_children(self, cache=None, verbose=False):
        self.make_Z_matrix(verbose=verbose)
        self.make_kernel(verbose=verbose)
        self.make_partition(verbose=verbose)
        self.make_children(cache=cache, verbose=verbose)
        # free some memory
        self.kernel_Z_basis = None
        self.Z_matrix = None

    def homology_fgmod(self, sparse=True, base_ring=None, check=True, verbose=False):
        if self.cached_homology is not None:
            # if verbose:
            #     print(".", end='', flush=True)
            return self.cached_homology
        if verbose:
            print()
            print("calculating homology")

        if base_ring is None:
            base_ring = ZZ
        incoming_total = sum(len(child.idempotent_list) for child in self.children)
        my_total = len(self.idempotent_list)
        assert my_total == sum(len(child.target_idempotent_list) for child in self.children)
        outgoing_total = len(self.target_idempotent_list)

        # Tensor with Z
        outgoing_matrix = Matrix(base_ring, outgoing_total, my_total, sparse=sparse)
        incoming_matrix = Matrix(base_ring, my_total, incoming_total, sparse=sparse)

        for i, row in enumerate(self.outgoing_right_mul_matrix):
            for j, cell in enumerate(row):
                outgoing_matrix[i,j] = sum(map(ig0, cell))
        
        running_incoming_index = 0
        for bindex, child in enumerate(self.children):
            right_mul_matrix = child.outgoing_right_mul_matrix
            my_idempotent_indexes_for_this_summand = self.partition_of_idempotents[bindex]
            assert len(my_idempotent_indexes_for_this_summand) == len(child.target_idempotent_list)

            for i, row in enumerate(right_mul_matrix):
                for j, cell in enumerate(row):
                    assert j < len(child.idempotent_list)
                    incoming_matrix[my_idempotent_indexes_for_this_summand[i], running_incoming_index + j] += sum(map(ig0, cell))

            running_incoming_index += len(child.idempotent_list)

        cc = ChainComplex({1: outgoing_matrix,
                           2: incoming_matrix},
                           degree_of_differential=-1,
                           check=check,
                           base_ring=base_ring)
        h = cc.homology(1, verbose=verbose, base_ring=base_ring, generators=False, algorithm='dhsw')
        invariants = h.invariants()
        ab = FinitelyGeneratedAbelianGroup(*invariants)
        self.cached_homology = ab
        if verbose:
            print(f"calculated {h}")
        return ab
    
    def homology_with_offset(self, offset, cache, verbose=False):
        if offset in self.cached_homology_with_offset:
            return self.cached_homology_with_offset[offset]
        if self.children is None:
            self.prepare_and_make_children(cache=cache, verbose=verbose)
        if offset == 0:
            Hi = self.homology_fgmod(verbose=verbose)
        else:
            summands = [child.homology_with_offset(offset - 1, cache, verbose)
                        for child in self.children]
            Hi = FinitelyGeneratedAbelianGroup.direct_sum(*summands)
        self.cached_homology_with_offset[offset] = Hi
        return Hi

    def ZG_homology_fgmod(self, projection, Gop, sparse=True, check=True, verbose=False):
        if self.cached_ZG_homology is not None:
            return self.cached_ZG_homology
        nG = len(Gop)
        # if nG == 1:
        #     return self.homology_fgmod(self, sparse=sparse, check=check, verbose=verbose)

        incoming_total = sum(len(child.idempotent_list) for child in self.children)
        my_total = len(self.idempotent_list)
        assert my_total == sum(len(child.target_idempotent_list) for child in self.children)
        outgoing_total = len(self.target_idempotent_list)

        # Tensor with ZG
        outgoing_matrix = Matrix(ZZ, outgoing_total*nG, my_total*nG, sparse=sparse)
        incoming_matrix = Matrix(ZZ, my_total*nG, incoming_total*nG, sparse=sparse)

        for i, row in enumerate(self.outgoing_right_mul_matrix):
            for j, cell in enumerate(row):
                for coeff, s in cell:
                    g = projection[s]
                    for jj in range(nG):
                        ii = Gop[jj][g]
                        outgoing_matrix[i*nG+ii,j*nG+jj] += coeff

        running_incoming_index = 0
        for bindex, child in enumerate(self.children):
            right_mul_matrix = child.outgoing_right_mul_matrix
            my_idempotent_indexes_for_this_summand = self.partition_of_idempotents[bindex]
            assert len(my_idempotent_indexes_for_this_summand) == len(child.target_idempotent_list)
            for i, row in enumerate(right_mul_matrix):
                for j, cell in enumerate(row):
                    assert j < len(child.idempotent_list)
                    for coeff, s in cell:
                        g = projection[s]
                        for jj in range(nG):
                            ii = Gop[jj][g]
                            incoming_matrix[my_idempotent_indexes_for_this_summand[i]*nG+ii, (running_incoming_index + j)*nG + jj] += coeff

            running_incoming_index += len(child.idempotent_list)

        cc = ChainComplex({1: outgoing_matrix,
                           2: incoming_matrix},
                           degree_of_differential=-1,
                           check=check,
                           base_ring=ZZ)
        h = cc.homology(1, verbose=verbose, base_ring=ZZ, generators=False, algorithm='dhsw')
        invariants = h.invariants()
        ab = FinitelyGeneratedAbelianGroup(*invariants)
        self.cached_ZG_homology = ab
        if verbose:
            print(f"calculated {h}")
        return ab


class BranchedResolution:
    __slots__ = ["op", "e_to_Lclass", "dim_to_nodes", "construction_cache"]

    def __init__(self, op : list[list[int]]):
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

        # Augmentation from smallest left ideal
        min_e, min_L = min(self.e_to_Lclass.items(), key=lambda e_L: len(e_L[1]))
        Z_matrix = [[1] * len(min_L)]
        kernel_basis = get_kernel_basis(Z_matrix, len(min_L))
        input_gens, right_mul_matrix = get_cover_by_mapping([min_e], kernel_basis, op, self.e_to_Lclass)

        self.dim_to_nodes = [
            None, # dimension 0
            [ResolutionNode(op, self.e_to_Lclass, input_gens, [min_e], right_mul_matrix)],
        ]
        self.construction_cache = {}

    def extend(self, maxdim, verbose=False):
        while len(self.dim_to_nodes) - 1 < maxdim:
            if verbose:
                print(f"Extending to dimension {len(self.dim_to_nodes)}")
            new_nodes = []
            for node in self.dim_to_nodes[-1]:
                if node.children is None:
                    if verbose:
                        print("preparing and making children", flush=True)
                    node.prepare_and_make_children(cache=self.construction_cache, verbose=verbose)
                else:
                    total = sum(len(c.idempotent_list) for c in node.children)
                    # if verbose and total > 0:
                    #     print(f"children already exist with a total of {total} idempotents", flush=True)
                new_nodes.extend(node.children)
            self.dim_to_nodes.append(new_nodes)


    def homology_list(self, maxdim, verbose=False):
        self.extend(maxdim + 1, verbose=verbose)
        if verbose:
            print("done extending; finding homologies")
        homology_summands = {
            dim: [node.homology_fgmod(verbose=verbose) for node in self.dim_to_nodes[dim]]
            for dim in range(1, maxdim + 1)
        }
        if verbose:
            print("recombining...")
        hl = []
        for dim, summands in homology_summands.items():
            if verbose:
                print(f"{len(summands)=}; {sum(s.free_rank for s in summands)=}")
            fgmod = FinitelyGeneratedAbelianGroup.direct_sum(*summands)
            h = fgmod.sage_string()
            hl.append(h)

            # if verbose:
            #     print(f"{len(invariants)=}...", end='', flush=True)
            # # Make them actually invariant:
            # additive = AdditiveAbelianGroup(invariants, remember_generators=False)
            # invariants = additive.invariants()
            # h = HomologyGroup(len(invariants), ZZ, invariants)
            # if verbose:
            #     print(f"done")
            # hl.append(h)
        # return hl
        return ", ".join(hl).join("[]")

    def ZG_homology_list(self, maxdim, verbose=False):
        self.extend(maxdim + 1, verbose=verbose)
        if verbose:
            print("done extending; finding homologies")
        from .structure_utils import group_completion
        projection, Gop = group_completion(self.op)

        cover_homology_summands = {
            dim: [node.ZG_homology_fgmod(projection, Gop, verbose=verbose) for node in self.dim_to_nodes[dim]]
            for dim in range(1, maxdim + 1)
        }
        if verbose:
            print("recombining...")
        hl = []
        for dim, summands in cover_homology_summands.items():
            if verbose:
                print(f"{len(summands)=}; {sum(s.free_rank for s in summands)=}")
            fgmod = FinitelyGeneratedAbelianGroup.direct_sum(*summands)
            h = fgmod.sage_string()
            hl.append(h)
        # return hl
        return ", ".join(hl).join("[]")

    def pi2(self, verbose=False):
        self.extend(3)
        summands = [node.ZG_homology_fgmod(verbose=verbose) for node in self.dim_to_nodes[2]]
        return FinitelyGeneratedAbelianGroup.direct_sum(*summands).sage_string()

    def homology_list_v2(self, maxdim, verbose=False):
        [C1] = self.dim_to_nodes[1]
        cache = {}
        hl = [C1.homology_with_offset(offset=offset, cache=cache, verbose=verbose).sage_string()
              for offset in range(maxdim)]
        return ", ".join(hl).join("[]")


def find_good_branched_resolution(op0, peek_dim=4, verbose=False):
    """Choose a few different versions of a monoid operation,
    and compute some projective resolutions up to `peek_dim`.
    Return the smallest one.
    """
    verbose = False
    n = len(op0)
    n_1 = n - 1
    rn = range(n)
    ops = [
        [[op0[i][j] for j in rn] for i in rn],
        [[op0[j][i] for j in rn] for i in rn],
        [[n_1 - op0[n_1 - i][n_1 - j] for j in rn] for i in rn],
        [[n_1 - op0[n_1 - j][n_1 - i] for j in rn] for i in rn],
    ]
    resolutions = [BranchedResolution(op) for op in ops]

    for dim in range(2, peek_dim + 1):
        for res in resolutions:
            res.extend(dim, verbose=verbose)
            if len(res.dim_to_nodes[-1]) == 0:
                if verbose:
                    print("short circuit: finite resolution!")
                return res
    if verbose:
    # if 1:
        print("numbers of nodes:", [len(res.dim_to_nodes[-1]) for res in resolutions])

    def uniqueness(res):
        lasts = set(res.dim_to_nodes[-1])
        for node_list in res.dim_to_nodes[1:-1]:
            lasts.difference_update(node_list)
        return sum(len(x.idempotent_list) for x in lasts)
    best = min(resolutions, key=uniqueness)
    if verbose:
        print(f"picked best with {len(best.dim_to_nodes[-1])} nodes.")
    return best
