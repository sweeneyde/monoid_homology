import sys
from itertools import product, permutations
from collections import defaultdict

sys.path.append("/mnt/c/Users/Owner/Desktop/monoid_homology/")
from monoid_homology.structure_utils import (
    table_from_opfunc_and_set,
    product_op,
    get_kernel_structure,
    group_completion,
    get_kernel_R_and_L_classes,
)

def make_cyclic_group(n):
    return [[(i + j) % n for j in range(n)] for i in range(n)]

SMALL_GROUPS = {
    "1": [[0]],
    "C2": make_cyclic_group(2),
    "C3": make_cyclic_group(3),
    "C4": make_cyclic_group(4),
    "V4": product_op(make_cyclic_group(2), make_cyclic_group(2)),
    "C5": make_cyclic_group(5),
    "C6": make_cyclic_group(6),
    "D6": [[0,1,2,3,4,5],[1,0,4,5,2,3],[2,5,0,4,3,1],[3,4,5,0,1,2],[4,3,1,2,5,0],[5,2,3,1,0,4]],
    "C7": make_cyclic_group(7),

    "C8": make_cyclic_group(8),
    "C4C2": product_op(make_cyclic_group(4), make_cyclic_group(2)),
    "C2C2C2": product_op(product_op(make_cyclic_group(2), make_cyclic_group(2)), make_cyclic_group(2)),
    "D8": [[0,1,2,3,4,5,6,7],[1,3,4,6,7,2,0,5],[2,5,0,7,6,1,4,3],[3,6,7,0,5,4,1,2],[4,2,1,5,0,3,7,6],[5,7,6,4,3,0,2,1],[6,0,5,1,2,7,3,4],[7,4,3,2,1,6,5,0]],
    "Q8": [[0,1,2,3,4,5,6,7],[1,0,3,2,5,4,7,6],[2,3,1,0,6,7,5,4],[3,2,0,1,7,6,4,5],[4,5,7,6,1,0,2,3],[5,4,6,7,0,1,3,2],[6,7,4,5,3,2,1,0],[7,6,5,4,2,3,0,1]],
    "C9": make_cyclic_group(9),
    "C3C3": product_op(make_cyclic_group(3), make_cyclic_group(3)),

    "C10": make_cyclic_group(10),
    "D10": [[0,1,2,3,4,5,6,7,8,9],[1,3,4,6,7,2,9,8,5,0],[2,5,0,8,9,1,7,6,3,4],[3,6,7,9,8,4,0,5,2,1],[4,2,1,5,0,3,8,9,6,7],[5,8,9,7,6,0,4,3,1,2],[6,9,8,0,5,7,1,2,4,3],[7,4,3,2,1,6,5,0,9,8],[8,7,6,4,3,9,2,1,0,5],[9,0,5,1,2,8,3,4,7,6]],

    "C11": make_cyclic_group(11),
}


#########################################################################

def perm_inv(g):
    ginv = [None] * len(g)
    for i, x in enumerate(g):
        ginv[x] = i
    return ginv

def act(op, g, flip):
    n = len(op)
    for row in op:
        assert len(row) == n
    assert len(g) == n
    ginv = perm_inv(g)

    if flip:
        return [[ginv[op[gj][gi]] for gj in g] for gi in g]
    else:
        return [[ginv[op[gi][gj]] for gj in g] for gi in g]

def canonicalize(op):
    best = min(act(op, g, e)
        for g in permutations(range(len(op)))
        for e in range(2)
    )
    return tuple(map(tuple, best))

#########################################################################

def make_simple_op(m, n, G_op, sandwich):
    elements = list(product(range(m), range(len(G_op)), range(n)))
    assert len(sandwich) == n
    for row in sandwich:
        assert len(row) == m
    def opfunc(i1_g1_j1, i2_g2_j2):
        i1, g1, j1 = i1_g1_j1
        i2, g2, j2 = i2_g2_j2
        return (i1, G_op[g1][G_op[sandwich[j1][i2]][g2]], j2)
    return table_from_opfunc_and_set(opfunc, elements)

def simples_all_sandwiches(m, n, G_op):
    [e] = [x for x in range(len(G_op)) if G_op[x][x]==x]
    # assert e == 0, G_op
    def all_sandwiches():
        rows_without_first = [[e] + list(row) for row in product(range(len(G_op)), repeat=m-1)]
        first_row = [e] * m
        for mat_without_first in product(rows_without_first, repeat=n-1):
            yield [first_row] + list(mat_without_first)
       
    for sandwich in all_sandwiches():
        yield make_simple_op(m, n, G_op, sandwich)

def all_simples_up_to(size, exclude_thins=False):
    for ker_size in range(1, size + 1):
        for group_size in range(1, ker_size + 1):
            if ker_size % group_size == 0:
                num_eggs = ker_size // group_size
                height_width_pairs = [
                    (q, num_eggs//q)
                    for q in range(1, num_eggs + 1)
                    if num_eggs % q == 0
                    and q <= num_eggs//q
                ]
                if exclude_thins:
                    height_width_pairs = [pair for pair in height_width_pairs if 1 not in pair]
                for group_name, G in SMALL_GROUPS.items():
                    if len(G) == group_size:
                        for m, n in height_width_pairs:
                            print(f"working on {m}_{n}_{group_name}...")
                            all_simples = list(simples_all_sandwiches(m, n, G))
                            if len(all_simples) == 1:
                                simples = all_simples
                            elif len(all_simples) == 2 and len(group_completion(all_simples[0])[1]) != len(group_completion(all_simples[1])[1]):
                                simples = all_simples
                            else:
                                simples = []
                                unique_canonicals = set()
                                for op in all_simples:
                                    canonical = canonicalize(op)
                                    if canonical not in unique_canonicals:
                                        unique_canonicals.add(canonical)
                                        simples.append(op)

                            if len(simples) == 1:
                                [only] = simples
                                yield f"{m}_{n}_{group_name}", only
                            else:
                                for i, op in enumerate(simples):
                                    yield f"{m}_{n}_{group_name}_sandwich{i}", op

#########################################################################

def stabilizer(op):
    return [(g,e)
            for g in permutations(range(len(op)))
            for e in range(2)
            if act(op, g, e) == op]

def symmetric_orbit_vectors(ker_op, n):
    # produce pairs of "acted upon" lists
    # [(i_0, j_0, v_0), ... (i_n3, j_n3, v_n3)]
    # that the real list ought to be compared to.
    for g0, e in stabilizer(ker_op):
        for rest in permutations(range(len(ker_op), n)):
            g = g0 + rest
            if e:
                yield g, e, [(gj, gi, gv) for gi in g for gj in g for gv in g]
            else:
                yield g, e, [(gi, gj, gv) for gi in g for gj in g for gv in g]

def symmetry_breakers(ker_op, n):
    n0 = len(ker_op)
    original_vec = [(i, j, v) for i in range(n) for j in range(n) for v in range(n)]
    for g, e, new_vec in symmetric_orbit_vectors(ker_op, n):
        # gop = act(ker_op, g[:n0], e)
        sub_original = []
        sub_new = []
        for x, y in zip(original_vec, new_vec):
            if x != y:
                xi, xj, xv = x
                yi, yj, yv = y
                if xi < n0 and xj < n0:
                    assert yi < n0 and yj < n0
                    assert (ker_op[xi][xj] == xv) == (ker_op[yi][yj] == yv)
                else:
                    sub_original.append(x)
                    sub_new.append(y)
        yield g, e, sub_original, sub_new    

#########################################################################

def minion_lines(simple_op, n):
    n0 = len(simple_op)
    R_classes, L_classes = get_kernel_R_and_L_classes(simple_op)
    assert len(set.union(*map(set, R_classes))) == n0
    assert len(set.union(*map(set, L_classes))) == n0

    yield "MINION 3"
    yield "**VARIABLES**"
    yield f"DISCRETE m[{n},{n}] {{0..{n-1}}}"
    yield f"DISCRETE m3[{n},{n},{n}] {{0..{n-1}}}"
    yield f"BOOL b[{n},{n},{n}]"
    yield "**SEARCH**"
    yield "PRINT [m]"
    yield "**CONSTRAINTS**"
    for i, j, v in product(range(n), repeat=3):
        yield f"reify(eq(m[{i},{j}],{v}), b[{i},{j},{v}])"
    
    yield ""
    yield "# Associativity"
    for i, j, k in product(range(n), repeat=3):
        yield f"watchelement(m[{i},_], m[{j},{k}], m3[{i},{j},{k}])"
        yield f"watchelement(m[_,{k}], m[{i},{j}], m3[{i},{j},{k}])"
    
    yield ""
    yield "# Literal values"
    for i in range(n0):
        for j in range(n0):
            yield f"eq(m[{i},{j}], {simple_op[i][j]})"

    yield ""
    yield "# R-class constraints"
    for x in range(n0, n):
        for R_class in R_classes:
            for r1 in R_class:
                yield (
                    f"watched-or({{"
                    + ",".join(f"eq(m[{r1},{x}],{r2})" for r2 in R_class)
                    + f"}})"
                )
    yield ""
    yield "# L-class constraints"
    for x in range(n0, n):
        for L_class in L_classes:
            for l1 in L_class:
                yield (
                    f"watched-or({{"
                    + ",".join(f"eq(m[{x},{l1}],{l2})" for l2 in L_class)
                    + f"}})"
                )

    yield ""
    yield "# Symmetry Breaking"
    for g, e, old_vec, new_vec in symmetry_breakers(simple_op, n):
        yield f"# {g}{'+flip' if e else ''}"
        old_vec_str = ",".join(f"b[{i},{j},{v}]" for i, j, v in old_vec)
        new_vec_str = ",".join(f"b[{i},{j},{v}]" for i, j, v in new_vec)
        yield f"lexleq[quick]([{old_vec_str}],"
        yield f"              [{new_vec_str}])"
    
    yield "**EOF**"

#########################################################################

import subprocess
import gzip

import pathlib
MINION_PATH = "/home/dennis/minion-v2.0-linux/minion"

def make_minion_file(minion_file_path, simple_op, n):
    with open(minion_file_path, "w") as f:
        for line in minion_lines(simple_op, n):
            print(line, file=f)

def run_minion(minion_file_path, solution_output_path):
    command = [
        MINION_PATH,
        str(minion_file_path),
        "-findallsols",
        "-noprintsols",
        "-solsout",
        str(solution_output_path),
    ]
    print(*command)
    result = subprocess.run(command, capture_output=True)
    # print("--- stderr ---")
    # print(result.stderr.decode("utf-8"))
    # print("--- stdout ---")
    # print(result.stdout.decode("utf-8"))
    result.check_returncode()

def transposed_solution(solution_output_path, n):
    transposed = [bytearray() for _ in range(n*n)]
    with open(solution_output_path) as f:
        for line in f:
            line = line.strip().replace(" ", "").encode("ascii")
            assert len(line) == n*n, line
            for i in range(n*n):
                transposed[i].append(line[i])
    assert len(set(map(len, transposed))) <= 1
    return [[transposed[i*n+j] for j in range(n)] for i in range(n)]

def dump_compressed_transposed_solution(transposed, n, transposed_path):
    with gzip.open(transposed_path, "wb") as f:
        for row in transposed:
            for entry in row:
                f.write(entry)
                f.write(b"\n")

def make_data_files(parent_folder : pathlib.Path, n, exclude_thins):
    folder = parent_folder / f"order{n}"
    folder.mkdir()
    total = 0
    name_to_count = {}
    for name, simple in all_simples_up_to(n, exclude_thins=exclude_thins):
        print(f"working on {name} with order {n}.")
        subfolder = folder / f"min_{name}"
        subfolder.mkdir()
        minion_file_path = subfolder / "search.minion"
        solution_output_path = subfolder / "minion_results.out"
        transposed_path = subfolder / "tables.dat.gz"
        # data_folder = subfolder / "table_data"
        # data_folder.mkdir()
        print("making minion file...")
        make_minion_file(minion_file_path, simple, n)
        print("running minion...")
        run_minion(minion_file_path, solution_output_path)
        print("transposing...")
        transposed = transposed_solution(solution_output_path, n)
        num_solutions = len(transposed[0][0])
        total += num_solutions
        name_to_count[name] = num_solutions
        print(f"Found {num_solutions} semigroups")
        with open(subfolder / "README.md", "w") as f:
            print(f"# Found {num_solutions} semigroups of order {n} with minimal ideal `{name}`", file=f)
        dump_compressed_transposed_solution(transposed, n, transposed_path)
    
    if exclude_thins:
        big_readme = f"# Found {total} total semigroups of order {n} excluding thin minimal ideals"
    else:
        big_readme = f"# Found {total} total semigroups of order {n}"
    with open(folder / "README.md", "w") as f:
        print(big_readme, file=f)
        print(file=f)
        for name, count in name_to_count.items():
            print(f"* {count} with minimal ideal `{name}`", file=f)
    print(f"Finished building {folder}")

def main():
    parent_folder = pathlib.Path("/home/dennis/data_by_min_ideal/")
    for n in (10,):
        make_data_files(parent_folder, n, exclude_thins=True)

if __name__ == "__main__":
    from time import time
    t0 = time()
    main()
    t1 = time()
    print(f"{t1-t0:.2f} seconds elapsed")
