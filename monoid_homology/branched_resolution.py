from collections import defaultdict
from bisect import bisect
from abelian_groups import FinitelyGeneratedAbelianGroup

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
            # D[i1]
            for jj in range(j, n):
                Di1[jj] += q*Di2[jj]
            D[i1], D[i2] = D[i2], D[i1]
            # Di1[:], Di2[:] = Di2[:], Di1[:]
            # for jj in range(j, n):
            #     Di2[jj] += q*Di1[jj]
            assert D[i1][j] == b
            assert D[i2][j] == 0
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

    def first_pass(k):

        if not any(True for i in range(k+1, m) if D[i][k]):
            if not any(True for j in range(k+1, n) if D[k][j]):
                if verbose:
                    print("pivot already good")
                return
        # Try to get a 1 in the pivot position as fast as possible.
        col_sums = [sum(abs(D[i][j]).bit_length() for i in range(k, m)) for j in range(k, n)]
        row_sums = [sum(abs(D[i][j]).bit_length() for j in range(k, n)) for i in range(k, m)]

        best_i, best_j = k, k
        best_nonzero = (D[k][k] == 0)
        best_abs = abs(D[k][k])
        best_sum = col_sums[0] + row_sums[0]

        for i in range(k, m):
            row_sum = row_sums[i-k]
            for j in range(k, n):
                Dij = D[i][j]
                this_nonzero = (Dij == 0)
                if not (this_nonzero <= best_nonzero):
                    continue
                this_abs = abs(Dij)
                if this_nonzero == best_nonzero and not (this_abs <= best_abs):
                    continue
                this_sum = col_sums[j-k] + row_sum
                if this_nonzero == best_nonzero and this_abs == best_abs and not (this_sum <= best_sum):
                    continue
                best_i, best_j = i, j
                best_nonzero = this_nonzero
                best_abs = this_abs
                best_sum = this_sum

        i, j = best_i, best_j
        # i, j = min(((i, j) for i in range(k, m) for j in range(k, n)), key=keyfunc)

        assert best_abs == abs(D[i][j]), (best_abs, D[i][j])

        D[k], D[i] = D[i], D[k]
        if j > k:
            improve_with_col_ops(k, j, k)
        
        assert best_abs == abs(D[k][k]), (best_abs, D[k][k])

        if verbose:
            print(f"{abs(D[k][k])=}, {col_sums[j-k]=}, {row_sums[i-k]=}")

        # best_i, best_j, best_key = k, k, keyfunc(k, k)
        # for i in range(k, m):
        #     for j in range(k, n):
        # i, j = min(((i, j) for i in range(k, m) for j in range(k, n)), key=lambda i_j: (D[i_j[0]][i_j[1]] == 0, abs()))
        # D[k+1:] = sorted(D[k+1:], key=lambda row: (row[k] == 0, abs(row[k]), max(map(abs, row))))
        # if D[k][k] not in {-1, 1}:
        #     for i in range(k, m):
        #         for j in range(k, n):
        #             if D[i][j] in {-1, 1}:
        #                 D[k], D[i] = D[i], D[k]
        #                 if j > k:
        #                     improve_with_col_ops(k, j, k)
        #                     return

    if verbose:
        from tqdm import tqdm
        range_mn = tqdm(range(min(m,n)), desc=f"SNF", dynamic_ncols=True, smoothing=0.0, ascii=True, miniters=0)
    else:
        range_mn = range(min(m,n))

    # make diagonal
    for k in range_mn:
        first_pass(k)
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
    D, T = partial_smithify(A, n, verbose=verbose)
    ker_D_indices = [j for j in range(n) if j >= m or D[j][j] == 0]
    columns = [
        [T[i][j] for i in range(n)]
        for j in ker_D_indices
    ]
    columns.sort(key=vec_sort_key)
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
                 "pivot_location_in_row"]

    def __init__(self, ambient_dimension):
        self.N = N = ambient_dimension
        self.pivot_location_in_column = [None] * N
        self.pivot_location_in_row = []
        self.basis = []

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

    def __contains__(self, vec0):
        """Does this subspace contain this vector?"""
        vec = vec0
        col_piv = self.pivot_location_in_column
        N = self.N
        basis = self.basis
        for j in range(N):
            if vec[j]:
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
                        # copy on write
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
            if vec[j]:
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
                    row[j:], vec[j:] = vec[j:], row[j:]
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


def cover_fast(output_gens, kernel_basis, op, e_to_Lclass, verbose=False):
    """
    Given a list `output_gens` of idempotents (e1, ..., en)
    and a list `kernel_basis` of vectors in

        Y := ZZ[S]e1 (+) ... (+) ZZ[S]en,

    produce a new module

        X := ZZ[S]f1 (+) ... (+) ZZ[S]fm

    and a ZZ[S]-linear map d: X --> Y
    such that d(X) = the ZZ-span of `kernel_basis`.

    This has the same API as cover(), but does not try very hard
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
    output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(e_to_Lclass[gen]))]
    output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
    N = len(output_index_pairs)

    def left_multiply_index(s, index):
        # Takes a one-hot Z-basis vector at index
        # and multiplies it on the left by the semigroup element s
        # to find the index of the result one-hot Z-basis vector
        (i, ii) = output_index_pairs[index]
        Lclass = e_to_Lclass[output_gens[i]]
        x = Lclass[ii]
        sx = op[s][x]
        ii_new = Lclass.index(sx)
        return output_index_pair_to_index[i, ii_new]
    left_multiply_index_table = [
        [left_multiply_index(s, index) for index in range(N)]
        for s in range(len(op))
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
        kernel_basis = tqdm(kernel_basis,
                            desc="cover",
                            # desc=f"dim{len(self.module_list)}",
                            dynamic_ncols=True, smoothing=0.0, ascii=True, miniters=1)

    for vec in kernel_basis:
        if vec not in covered:
            e = None
            for s in range(len(op)):
                svec = left_multiply_vector(s, vec)
                covered.add(svec)
                if s in e_to_Lclass and svec == vec:
                    if e is None or len(e_to_Lclass[s]) < len(e_to_Lclass[e]):
                        e = s
            assert e is not None, "Not a monoid?"
            input_gens.append(e)
            right_mul_column = [[] for _ in output_gens]
            for index, coeff in enumerate(vec):
                if coeff:
                    i, ii = output_index_pairs[index]
                    Lclass = e_to_Lclass[output_gens[i]]
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

def cover(output_gens, kernel_basis, op, e_to_Lclass, verbose=False):
    """
    Given a list `output_gens` of idempotents (e1, ..., en)
    and a list `kernel_basis` of vectors in

        X := ZZ[S]e1 (+) ... (+) ZZ[S]en,

    produce a new module

        Y := ZZ[S]f1 (+) ... (+) ZZ[S]fm

    and a ZZ[S]-linear map d: X --> Y
    such that d(X) = the ZZ-span of `kernel_basis`.

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

    output_index_pairs = [(i, ii) for i, gen in enumerate(output_gens) for ii in range(len(e_to_Lclass[gen]))]
    output_index_pair_to_index = {x: i for i, x in enumerate(output_index_pairs)}
    N = len(output_index_pairs)

    def left_multiply_index(s, index):
        # Takes a one-hot Z-basis vector at index
        # and multiplies it on the left by the semigroup element s
        # to find the index of the result one-hot Z-basis vector
        (i, ii) = output_index_pairs[index]
        Lclass = e_to_Lclass[output_gens[i]]
        x = Lclass[ii]
        sx = op[s][x]
        ii_new = Lclass.index(sx)
        return output_index_pair_to_index[i, ii_new]

    if verbose:
        print("making table...")
    left_multiply_index_table = [
        [left_multiply_index(s, index) for index in range(N)]
        for s in range(len(op))
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
        for s in range(len(op)):
            sub.add(left_multiply_vector(s, vec))
        ZS_spans.append(sub)

    idempotents_by_size = sorted(e_to_Lclass.keys(), key=lambda e: len(e_to_Lclass[e]))

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
                Lclass = e_to_Lclass[output_gens[i]]
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
            key=lambda kindex: len(inclusions[kindex]) / len(e_to_Lclass[kindex_to_e[kindex]])
        )
        num_added = len(e_to_Lclass[kindex_to_e[kindex]])
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
            num_added = len(e_to_Lclass[kindex_to_e[kindex]])
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

    # if verbose:
    #     print(f"done with dim{len(self.module_list)}")
    return input_gens, right_mul_matrix



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

    def make_Z_matrix(self, verbose=False):
        if verbose:
            print("making Z matrix", flush=True)
        assert self.Z_matrix is None
        matrix = [[0] * len(self.input_index_pairs) for _ in self.output_index_pairs]

        it = self.idempotent_list
        if verbose:
            from tqdm import tqdm
            it = tqdm(it, desc=f"Zmat", dynamic_ncols=True, smoothing=0.0, ascii=True, miniters=1)

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
        bins.sort()
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

        coverfunc = cover if len(my_kernel_vectors) <= 50 else cover_fast
        # coverfunc = cover_fast
        input_gens, incoming_right_mul_matrix = coverfunc(my_idempotents, my_kernel_vectors, self.op, self.e_to_Lclass, verbose=verbose)

        if cache is not None:
            key = (
                tuple(input_gens),
                tuple(my_idempotents),
                tuple(tuple(tuple(entry) for entry in row) for row in incoming_right_mul_matrix),
            )
            cached_child = cache.get(key)
            if cached_child is not None:
                # if verbose:
                #     print("cache hit")
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
        from operator import itemgetter
        ig0 = itemgetter(0)

        from sage.all import Matrix, ZZ, ChainComplex
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
        input_gens, right_mul_matrix = cover([min_e], kernel_basis, op, self.e_to_Lclass)

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
                    if verbose:
                        print(f"children already exist with a total of {sum(len(c.idempotent_list) for c in node.children)} idempotents", flush=True)
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

def find_good_branched_resolution(op0, peek_dim=4, verbose=False):
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
    resolutions = [BranchedResolution(op) for op in ops]

    for dim in range(2, peek_dim + 1):
        for res in resolutions:
            res.extend(dim, verbose=verbose)
            if len(res.dim_to_nodes[-1]) == 0:
                if verbose:
                    print("short circuit: finite resolution!")
                return res
    if verbose:
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
