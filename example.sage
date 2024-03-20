import multiprocessing as mp
from tqdm import tqdm
from collections import defaultdict
from time import perf_counter as now


sys.path.append("/mnt/c/Users/Owner/Desktop/monoid_homology/")
from monoid_homology import (
    op_from_id,
    find_best_gens_crs,
)

maxdim = 4
verbose = False
nelements = 7

def mp_process(ix):
    op = op_from_id(nelements, ix)
    crs = find_best_gens_crs(op, maxdim, verbose=verbose)
    hl = crs.homology_list(maxdim, algorithm='dhsw')
    return ix, str(hl)

def main():
    if 0:
        ix_list = range(1, 15973+1)
    if 0:
        ix_list = []
        with open(f"/home/dennis/{nelements}gen_homology.txt") as f:
            for line in f:
                ix, _, kind = line.strip().partition(" ")
                if kind == "[C2, 0, C2]":
                    ix_list.append(int(ix))
        print(f"{len(ix_list)=}")
    if 0:
        ix_list = [123]

    groupings = defaultdict(list)
    with mp.Pool(6) as pool:
        it = pool.imap_unordered(mp_process, ix_list)
        for ix, res in tqdm(it, total=len(ix_list)):
            # print(ix, res)
            # tqdm_ix_list.refresh()
            groupings[res].append(ix)

    for res, ixs in groupings.items():
        ixs.sort()
        print(res, ":", ",".join(map(str, ixs)))
    return groupings

if __name__ == "__main__":
    t0 = now()
    groupings = main()
    t1 = now()
    print(t1 - t0, "seconds elapsed")

