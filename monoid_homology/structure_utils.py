from collections import defaultdict
from itertools import permutations, product
import math

def table_from_opfunc_and_set(opfunc, opset):
    elements = list(opset)
    element_to_index = {x: i for i, x in enumerate(elements)}
    return [
        [
            element_to_index[opfunc(xi, xj)]
            for xj in elements
        ]
        for xi in elements
    ]

def product_op(op1, op2):
    opset = {(x, y) for x in range(len(op1)) for y in range(len(op2))}
    def opfunc(x1y1, x2y2):
        x1, y1 = x1y1
        x2, y2 = x2y2
        return (op1[x1][x2], op2[y1][y2])
    return table_from_opfunc_and_set(opfunc, opset)

def adjoin_1(op):
    op1 = [list(row) for row in op]
    for i, row in enumerate(op1):
        row.append(i)
    op1.append(list(range(len(op) + 1)))
    return op1

def get_identity(op):
    rn = range(len(op))
    for e in rn:
        if all(op[e][x] == x == op[x][e] for x in rn):
            return e
    return None

def is_monoid(op):
    return get_identity(op) is not None

def maybe_adjoin_1(op):
    rn = range(len(op))
    for e in rn:
        if all(op[e][x] == x == op[x][e] for x in rn):
            return op
    return adjoin_1(op)

def _get_all_product(op):
    p = 0
    for x in range(1, len(op)):
        p = op[p][x]
    return p

def get_zero(op):
    p = _get_all_product(op)
    for x in range(len(op)):
        if op[p][x] != p or op[x][p] != p:
            return None
    return p

def _get_kernel_RL(op):
    p = _get_all_product(op)
    R = {op[p][x] for x in range(len(op))}
    L = {op[x][p] for x in range(len(op))}
    return R, L

def get_kernel_height_width_G(op):
    """Given a multiplication table,
    return the size of the kernel (minimum ideal)
    as a tuple (height, width, G), where:
        height is the number of R-classes
        width is the number of L-classes
        G is some particular H-class
    The overall size of the kernel is then the product of these.
    """
    R, L = _get_kernel_RL(op)
    G = L & R
    depth = len(G)
    width = len(R) // depth
    height = len(L) // depth
    return (height, width, G)

def restrict_to_subset(op, subset):
    new_to_old = list(subset)
    old_to_new = {x: i for i, x in enumerate(new_to_old)}
    return [
        [
            old_to_new[op[old_i][old_j]]
            for old_j in new_to_old
        ]
        for old_i in new_to_old
    ]

def thin_equivalent(op):
    height, width, G = get_kernel_height_width_G(op)
    if height == 1 or width == 1:
        return restrict_to_subset(op, G)
    else:
        return None

def equivalent_submonoid(op):
    equiv = thin_equivalent(op)
    if equiv is not None:
        return equiv
    monoid_one_sided_ideals = []
    rn = range(len(op))
    for e in rn:
        if op[e][e] == e:
            eS = {op[e][x] for x in rn}
            if all(op[ex][e] == ex for ex in eS):
                monoid_one_sided_ideals.append(eS)
                continue
            Se = {op[x][e] for x in rn}
            if all(op[e][xe] == xe for xe in Se):
                monoid_one_sided_ideals.append(Se)
                continue
    if not monoid_one_sided_ideals:
        return op
    submon = min(monoid_one_sided_ideals, key=len)
    if len(submon) == len(op):
        return op
    else:
        equiv = restrict_to_subset(op, submon)
        return equivalent_submonoid(equiv)

def group_identity_and_inverses(op, G):
    [e] = [g for g in G if op[g][g] == g]
    # Thanks to Alex Li for the idea of doing this in linear time!
    inv = {e: e}
    for g in G:
        if g in inv:
            continue
        powers = [e, g]
        while (h := powers[-1]) not in inv:
            powers.append(op[h][g])
        hinv = inv[h]
        # If |g|=n and h=g^k
        # Then (g^i)^(-1) = g^(n-i) = g^(n-k)g^(k-i) = h^(-1) g^(k-i)
        for x, y in zip(powers, reversed(powers)):
            xinv = op[hinv][y]
            inv[x] = xinv
            inv[xinv] = x
    return e, inv

class UnionFind:
    def __init__(self, objects):
        self.objects = objects
        self.parent = {obj:obj for obj in objects}
        self.size = {obj:obj for obj in objects}

    def find(self, x):
        # Amortized runtime: O(alpha(len(objects)))
        # Path splitting
        p = self.parent
        while p[x] != x:
            x, p[x] = p[x], p[p[x]]
        return x

    def union(self, x, y):
        x = self.find(x)
        y = self.find(y)
        if x == y:
            return
        if self.size[x] < self.size[y]:
            x, y = y, x
        self.parent[y] = x
        self.size[x] += self.size[y]

    def component(self, x):
        x = self.find(x)
        return {y for y in self.objects if self.find(y) == x}


def generated_subgroup(G, op, e, X):
    # (G, operation) is a group with identity e
    # X is a subset of G
    u = UnionFind(G)
    for x in X:
        if u.find(e) != u.find(x):
            for g in G:
                u.union(g, op[g][x])
    return u.component(e)

def find_generators(G, op, e):
    generators = []
    u = UnionFind(G)
    for gen in G:
        if u.find(e) != u.find(gen):
            generators.append(gen)
            for g in G:
                u.union(g, op[g][gen])
    return generators

def find_conjugates(G, op, e, inv, X):
    # (G, operation) is a group
    # e is the identity
    # inverse is a function that finds the inverse of an element.
    # X is a subset of $G$.
    if not X:
        return set()

    generators = find_generators(G, op, e)
    u = UnionFind(G) # relate conjugates
    for gen in generators:
        gen_inv = inv[gen]
        for g in G:
            u.union(g, op[gen][op[g][gen_inv]])
    # Now all conjugates are related.
    # Relate all elements of X so that there is just one component
    # to worry about.
    x0 = next(iter(X)) # arbitrary element of X
    for x in X:
        u.union(x0, x)
    return u.component(x0)

def normal_closure(G, op, e, inv, X):
    assert set(X) <= set(G)
    conjugates = find_conjugates(G, op, e, inv, X)
    return generated_subgroup(G, op, e, conjugates)

def group_quotient_by_subset(op, G, to_kill):
    e, inv = group_identity_and_inverses(op, G)
    N = normal_closure(G, op, e, inv, to_kill)
    return group_quotient_by_normal(op, G, N)

def group_quotient_by_normal(op, G, N):
    cells = [N]
    remaining = set(G) - N
    while remaining:
        g = remaining.pop()
        cell = {op[g][N_element] for N_element in N}
        remaining -= cell
        cells.append(cell)
    G_to_result = {g: i for i, cell in enumerate(cells) for g in cell}
    cell_reps = [next(iter(cell)) for cell in cells]
    result_op = [
        [G_to_result[op[g1][g2]] for g2 in cell_reps]
        for g1 in cell_reps
    ]
    return G_to_result, result_op

def get_kernel_structure(op):
    R, L = _get_kernel_RL(op)
    G = R & L
    X = [g for g in L if op[g][g] == g]
    Y = [g for g in R if op[g][g] == g]
    sandwich = {(y, x) : op[y][x] for y in Y for x in X}
    return X, G, Y, sandwich

def get_kernel_elements(op):
    X, G, Y, _ = get_kernel_structure(op)
    K = {op[x][op[g][y]] for x in X for g in G for y in Y}
    assert len(K) == len(X) * len(G) * len(Y)
    return K

def get_kernel_R_and_L_classes(op):
    R, L = _get_kernel_RL(op)
    G = R & L
    X = [g for g in L if op[g][g] == g]
    Y = [g for g in R if op[g][g] == g]
    R_classes = [
        [op[x][r] for r in R]
        for x in X
    ]
    L_classes = [
        [op[l][y] for l in L]
        for y in Y
    ]
    kernel_size = len(X)*len(Y)*len(G)
    assert sum(map(len, R_classes)) == kernel_size
    assert sum(map(len, L_classes)) == kernel_size
    assert len(set.union(*map(set, R_classes))) == kernel_size
    assert len(set.union(*map(set, L_classes))) == kernel_size
    return R_classes, L_classes

def group_completion(op):
    X, G, Y, sandwich = get_kernel_structure(op)
    G_to_result, result_op = group_quotient_by_subset(op, G, set(sandwich.values()))
    [e] = [g for g in G if op[g][g] == g]
    projection = [G_to_result[op[e][op[x][e]]] for x in range(len(op))]
    return projection, result_op

def op_has_ptorsion(op, p):
    assert p in {2,3,5,7,11,13,17,19}
    if len(op) < p:
        return False
    rp1 = range(p-1)
    for x in range(len(op)):
        xp = x
        for _ in rp1:
            xp = op[xp][x]
        if xp != x and op[xp][xp] == xp and op[xp][x] == x:
            return True
    return False

def is_regular(op):
    rn = range(len(op))
    for a in rn:
        for x in rn:
            if op[op[a][x]][a] == a:
                break
        else:
            # No break: `a` has no pseudoinverse
            return False
    # Every `a` had a pseudoinverse
    return True

def get_L_classes(op):
    generated_to_generator = defaultdict(list)
    rn = range(len(op))
    for x in rn:
        Sx = {op[y][x] for y in rn}; Sx.add(x)
        generated_to_generator[frozenset(Sx)].append(x)
    return list(generated_to_generator.values())

def get_R_classes(op):
    generated_to_generator = defaultdict(list)
    rn = range(len(op))
    for x in rn:
        xS = {op[x][y] for y in rn}; xS.add(x)
        generated_to_generator[frozenset(xS)].append(x)
    return list(generated_to_generator.values())

def get_H_classes(op):
    generated_to_generator = defaultdict(list)
    rn = range(len(op))
    for x in rn:
        Sx = {op[y][x] for y in rn}; Sx.add(x)
        xS = {op[x][y] for y in rn}; xS.add(x)
        generated_to_generator[frozenset(Sx), frozenset(xS)].append(x)
    return list(generated_to_generator.values())

def _one_swap(op, s1, s2):
    s = lambda x: {s1:s2, s2:s1}.get(x, x)
    n = len(op)
    new_op = [[None]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            new_op[i][j] = s(op[s(i)][s(j)])
    return new_op

def transpose_op(op):
    return list(map(list, zip(*op)))

def swaps(op, *ss, T=False):
    for s1, s2 in ss:
        op = _one_swap(op, s1, s2)
    if T:
        op = transpose_op(op)
    return op

def _perm_inv(g):
    ginv = [None] * len(g)
    for i in range(len(g)):
        ginv[g[i]] = i
    return ginv

def _act(op, g, flip):
    n = len(op)
    for row in op:
        assert len(row) == n
    assert len(g) == n
    ginv = _perm_inv(g)

    if flip:
        return [[ginv[op[gj][gi]] for gj in g] for gi in g]
    else:
        return [[ginv[op[gi][gj]] for gj in g] for gi in g]

def canonicalize(op, allow_flip=True, fix=()):
    from itertools import permutations

    best = min(_act(op, g, e)
        for g in permutations(range(len(op)))
        for e in ((False, True) if allow_flip else (False,))
        if all(g[i] in fix for i in fix)
    )
    return best

def _find_order(op, x):
    y = x
    seen = {x: 1}
    tries = 1
    while True:
        y = op[y][x]
        tries += 1
        if y in seen:
            return (seen[y], tries)
        else:
            seen[y] = tries

def _element_data(op, x):
    rn = range(len(op))
    Sx = {op[s][x] for s in rn}
    xS = {op[x][s] for s in rn}
    return (min(len(Sx), len(xS)), len(Sx) + len(xS), len(Sx & xS), *_find_order(op, x))

def canonicalize_faster(op0):
    n = len(op0)
    groupings = defaultdict(list)
    for x in range(n):
        groupings[_element_data(op0, x)].append(x)
    groups = [groupings[kind] for kind in sorted(groupings.keys())]
    cost = math.prod(map(math.factorial, map(len, groups)))
    # if cost > 1000:
    #     from .fast_canonicalize import canonicalize as green_canonicalize
    #     print(f"{cost=}")
    #     canon = green_canonicalize(op0)
    #     return tuple(map(tuple, canon))
    best = None
    for perms in product(*map(permutations, groups)):
        g = sum(perms, ())
        ginv = _perm_inv(g)
        op1 =  [[ginv[op0[gi][gj]] for gj in g] for gi in g]
        if best is None or op1 < best:
            best = op1
        op1 = [[ginv[op0[gj][gi]] for gj in g] for gi in g]
        if op1 < best:
            best = op1
    return tuple(map(tuple, best))

def quotient_by_min_ideal(op):
    K = get_kernel_elements(op)
    def opfunc(a, b):
        if a == "K" or b == "K":
            return "K"
        ab = op[a][b]
        return "K" if ab in K else ab
    return table_from_opfunc_and_set(opfunc, (set(range(len(op))) - K) | {"K"})
