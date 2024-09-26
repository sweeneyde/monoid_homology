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

def normal_subgroup_generated_by(op, G, subset):
    assert set(subset) <= set(G)
    e, inv = group_identity_and_inverses(op, G)
    Ngen = {op[op[g][p]][inv[g]] for p in subset for g in G}
    Ngen.discard(e)
    N = set()
    stack = [e]
    while stack:
        N_element = stack.pop()
        if N_element in N:
            continue
        N.add(N_element)
        if len(N) * 2 > len(G):
            N = set(G)
            break
        for ngen in Ngen:
            stack.append(op[N_element][ngen])
    assert e in N
    return N

def group_quotient(op, G, to_kill):
    N = normal_subgroup_generated_by(op, G, to_kill)
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

def group_completion(op):
    X, G, Y, sandwich = get_kernel_structure(op)
    G_to_result, result_op = group_quotient(op, G, set(sandwich.values()))
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

