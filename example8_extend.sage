import multiprocessing as mp
from collections import defaultdict
from time import perf_counter as now
from datetime import datetime

from itertools import islice

def nowstring():
    return datetime.now().isoformat(timespec='seconds').replace(":", "_")

import sys
sys.path.append("/mnt/c/Users/Owner/Desktop/monoid_homology/")
from monoid_homology import (
    all_ops,
    op_from_id,
    find_best_gens_crs,
    string_to_op,
    all_gens_crs,
)

def mp_process(line):
    ix, _, opstring = line.partition(" ")
    ix = int(ix)
    op = string_to_op(opstring)
    # crs = all_gens_crs(op)
    crs = find_best_gens_crs(op, maxdim, verbose=verbose, extra=extra_search)
    counts = crs.essential_counts(maxdim + int('1'))
    if ix:
        print(ix, counts)
    try:
        # if max(counts) >= 1500:
        #     algorithm = "auto"
        # else:
        #     algorithm = "pari"
        # cc = crs.SAGE_chain_complex(up_to_dimension=maxdim + 1, check=False, verbose=verbose, sparse=False)
        # h = cc.homology(deg=3,
        #                 verbose=verbose,
        #                 algorithm='auto')
        # return ix, f"[C2, 0, {h}]"
        # h = 
        hl = crs.homology_list(maxdim, algorithm="auto", verbose=verbose, base_ring=GF(2))
        hl = str(hl).replace("Vector space of dimension ", "dim ").replace("Rational Field", "QQ").replace("Finite Field of size 2", "GF(2)")
        # print(ix, hl)
    except:
        print(f"error at {ix=}")
        raise
    return ix, str(hl)

maxdim = int('7')
verbose = False
show_progress = True
extra_search = int('1')

# def save_progress(groupings):
#     lines = []
#     for res, ixs in sorted(groupings.items(), key=lambda item: (len(item[1]), item[0]), reverse=True):
#         ixs.sort()
#         lines.append(f"{res} : " + ",".join(map(str, ixs)))
#     with open(f"dumps/dump8_unfinished.txt", "w") as dumpfile:
#         for line in lines:
#             print(line, file=dumpfile)

# def load_progress():
#     groupings = defaultdict(list)
#     with open(f"dumps/dump8_unfinished.txt") as dumpfile:
#         for line in dumpfile:
#             hl, arr = line.split(" : ")
#             groupings[hl] = [int(x) for x in arr.split(",")]
#     return groupings

def main():
    mp.set_start_method('spawn')




    # with open("dumps/8element_2hom.txt") as f:
    #     label, rest = next(iter(f)).split(" : ")
    #     assert label == "[C2, 0]"
    # ix_set = set(map(int, rest.split(",")))
    # del rest

    # ix_set = set()
    # with open("data/8elt_nonzeros/1_100000000.txt") as f:
    #     for line in f:
    #         ix, _, arrstr = line.partition(" ")
    #         op = string_to_op(arrstr)
    #         rn = range(len(op))
    #         if all(sum(op[op[i][j]][i] == i and op[op[j][i]][j] == j for j in rn) == 1 for i in rn):
    #             ix_set.add(int(ix))
    # print(",".join(map(str, sorted(ix_set))))
    # print(len(ix_set))
    # quit()

    # ix_set = set()
    # with open("/mnt/c/Users/Owner/Desktop/monoid_homology/8elt_data.txt") as f:
    #     for line in f:
    #         label, rest = line.split(" : ")
    #         ix_set.update(map(int, rest.split(",")))
    # with open("data/8elt_nonzeros/1_100000000.txt") as f:
    #     with open("data/8elt_semi_subset.txt", "w") as fout:
    #         for line in f:
    #             ix = int(line[:line.find(" ")])
    #             if ix in ix_set:
    #                 fout.write(line)
    # quit()

    ix_set = set()
    total = len(ix_set)
    # total = int('1_573_467')
    # print(ix_set)

    groupings = defaultdict(list,
    {
    })
    # groupings = load_progress()
    for arr in groupings.values():
        ix_set.difference_update(arr)
    print(ix_set)
    # groupings = defaultdict(list)

    def generate():
        with open("data/8elt_nonzeros/1_100000000.txt") as f:
            # for line in islice(f, 0, None, 10_000):
                # yield line
            for line in f:
                ix = int(line[:line.find(" ")])
                if ix in ix_set:
                    yield line

    try:
        # num_done = 0
        with mp.Pool(12) as pool:
            it = pool.imap_unordered(mp_process, generate())
        # if 1:
            # it = map(mp_process, generate())
            if show_progress:
                from tqdm import tqdm
                initial = sum(map(len, groupings.values()))
                it = tqdm(it, initial=initial, total=total, smoothing=float('0.0'), dynamic_ncols=True, miniters=1, mininterval=0.0)

            for ix, res in it:
                groupings[res].append(ix)
                ix_set.remove(ix)
                if 1:
                # if res != "[C2, 0, C2]":
                    if show_progress:
                        it.write(f"{ix} {res}")
                    else:
                        print(f"{ix} {res}")
                # num_done += 1
                # if num_done % 1_000 == 0:
                #     save_progress(groupings)
                #     it.write("saved progress.")
    except:
        print("HALTING EARLY!")
        # save_progress(groupings)
        with open(f"dumps/dump_{nowstring()}_unfinished.txt", "w") as dumpfile:
            for res, ixs in sorted(groupings.items(), key=lambda item: (len(item[1]), item[0]), reverse=True):
                ixs.sort()
                print(res, ":", ",".join(map(str, ixs)))
                print(res, ":", ",".join(map(str, ixs)), file=dumpfile)
        print(f"not done: {ix_set}")
        raise
    if ix_set:
        raise AssertionError(ix_set)
    # save_progress(groupings)
    with open(f"dumps/dump8_{nowstring()}.txt", "w") as dumpfile:
        for res, ixs in sorted(groupings.items(), key=lambda item: (len(item[1]), item[0]), reverse=True):
            ixs.sort()
            print(res, ":", ",".join(map(str, ixs)))
            print(res, ":", ",".join(map(str, ixs)), file=dumpfile)

    return groupings

if __name__ == "__main__":
    # import cProfile
    # with cProfile.Profile() as pr:
    #     main()
    # pr.print_stats(sort='time')
    # print("=" * 1000)
    # pr.print_stats(sort='cumtime')
        
    t0 = now()
    groupings = main()
    t1 = now()
    print(t1 - t0, "seconds elapsed")

