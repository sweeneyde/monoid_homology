import gzip
import sys
from pathlib import Path
from collections import defaultdict
from functools import lru_cache

sys.path.append("/mnt/c/Users/Owner/Desktop/monoid_homology/")
from monoid_homology import (
    find_good_resolution,
    maybe_adjoin_1,
)

@lru_cache(maxsize=1)
def data_from_gz(n, filename):
    print()
    print("reading from file...", end='')
    with gzip.open(filename, "rb") as f:
        data = f.read().splitlines()
    print("done")
    num = len(data[0])
    assert len(data) == n * n
    for packed in data:
        assert len(packed) == num
    return data


def iterate_from_gz(n, filename):
    data = data_from_gz(n, str(filename))
    num = len(data[0][0])
    rn = range(n)
    range_num = range(num)
    for index in range_num:
        yield index, [
            [int(data[i*n + j][index:index+1])
             for j in rn
            ]
            for i in rn
        ]

def subset_from_gz(n, filename, indexes):
    data = data_from_gz(n, str(filename))
    rn = range(n)
    for index in sorted(indexes):
        yield index, [
            [int(data[i*n + j][index:index+1])
             for j in rn
            ]
            for i in rn
        ]

def get_homology(ix_op):
    ix, op = ix_op
    res = find_good_resolution(maybe_adjoin_1(op), peek_dim=PEEKDIM, verbose=VERBOSE)
    return ix, str(res.homology_list(MAXDIM, verbose=VERBOSE))


PARENT_FOLDER = Path("/mnt/c/Users/Owner/Desktop/monoid_homology/data_by_min_ideal/")


def main_initialize():
    import multiprocessing as mp
    import tqdm

    mp.set_start_method("spawn")
    with mp.Pool(CORES) as pool:
        for n in (10,):
            folder = PARENT_FOLDER / f"order{n}"
            assert folder.is_dir()
            for subfolder in folder.iterdir():
                if subfolder.is_dir():
                    readme = (subfolder / "README.md").read_text()
                    total = int(readme.partition(" semigroups")[0].partition("Found ")[2])
                    print("working on", str(subfolder))
                    groupings = defaultdict(list)
                    it = iterate_from_gz(n, subfolder / "tables.dat.gz")
                    it = pool.imap_unordered(get_homology, it, chunksize=100)
                    it = tqdm.tqdm(it, smoothing=0.0, miniters=1, dynamic_ncols=True, total=total)
                    for ix, hl in it:
                        groupings[hl].append(ix)
                    for arr in groupings.values():
                        arr.sort()
                    with open(subfolder / "groupings.txt", "w") as fout:
                        for label, arr in groupings.items():
                            arr.sort()
                            print(label, ":", ",".join(map(str,arr)), file=fout)

import contextlib

def main_refine(n, min_ideal_name, homology_kind):
    folder = PARENT_FOLDER / f"order{n}"
    assert folder.is_dir()
    subfolder = folder / min_ideal_name
    assert subfolder.is_dir()
    with open(subfolder / "groupings.txt") as fin:
        lines = [line for line in fin if line.startswith(homology_kind)]
        assert len(lines) == 1, (len(lines), homology_kind, [line.partition(" : ")[0] for line in lines])
        [line] = lines
    label, arr = line.split(" : ")
    print("extending", label)
    if len(label.split(",")) >= MAXDIM:
        print("Already long enough.")
        return
    ix_set = list(map(int, arr.split(",")))
    
    pool = (mp.Pool(CORES) if CORES > 1 else contextlib.nullcontext())
    with pool as pool:
        it = subset_from_gz(n, subfolder / "tables.dat.gz", ix_set)
        if CORES > 1:
            it = pool.imap_unordered(get_homology, it, chunksize=100 if len(ix_set)>600_000 else 1)
        else:
            it = map(get_homology, it)
        it = tqdm.tqdm(it, smoothing=0.0, miniters=1, dynamic_ncols=True, total=len(ix_set))
        groupings = defaultdict(list)
        for ix, hl in it:
            if hl not in groupings:
                print("New split:", hl)
            groupings[hl].append(ix)

        for arr in groupings.values():
            arr.sort()
        groupings = dict(sorted(groupings.items(), key=lambda k_v: k_v[0]))
        if len(groupings) > 1:
            print("New splits:", label)
            for label in groupings:
                print("   ", label)
        else:
            for label in groupings:
                print("extended to", label)

        # with open(subfolder / "new_results.txt", "w") as fout:
        #     for label, arr in groupings.items():
        #         print(label, ":", ",".join(map(str,arr)), file=fout)
        
        old_file = subfolder / "groupings.txt"
        new_file = subfolder / "updated_groupings.txt"
        with open(new_file, "w") as fout:
            with open(old_file) as fin:
                found = False
                for line in fin:
                    if line.startswith(homology_kind):
                        assert not found
                        found = True
                        for label, arr in groupings.items():
                            print(label, ":", ",".join(map(str,arr)), file=fout)
                    else:
                        fout.write(line)

        if 1:
            lines = new_file.read_text().splitlines()
            lines.sort()
            with open(new_file, "w") as fout:
                for line in lines:
                    print(line, file=fout)
            del lines
        
        if 1:
            readme = (subfolder / "README.md").read_text()
            total = int(readme.partition(" semigroups")[0].partition("Found ")[2])
            seen = [False] * total
            with open(new_file) as f:
                for line in f:
                    arr = list(map(int, line[line.find(" : ")+3:].split(",")))
                    for x in arr:
                        if seen[x]:
                            raise AssertionError(f"more than one entry for{x}")
                        seen[x] = True
                if not all(seen):
                    i = seen.index(False)
                    raise AssertionError(f"no entry for {i}")
            print(f"All of range({total}) still accounted for")

        for label in groupings:
            assert label.startswith(homology_kind.rstrip(" :]"))
        print("consistent with previous results.")
    print("renaming...", end='')
    old_file.unlink()
    new_file.rename(old_file)
    print("done")

        


MAXDIM = 5
PEEKDIM = 3
CORES = 12
VERBOSE = False
# CHUNKSIZE=1

if __name__ == "__main__":

    import multiprocessing as mp
    import tqdm
    mp.set_start_method("spawn")

    # [(ix, op)] = subset_from_gz(9, "/mnt/c/Users/Owner/Desktop/monoid_homology/data_by_min_ideal/order9/min_2_2_1/tables.dat.gz", [128818])
    # print(";".join("".join(map(str, row)) for row in op))
    # res = find_good_resolution(maybe_adjoin_1(op), peek_dim=5)
    # print(res.homology_list(10))
    # for i, mod in enumerate(res.module_list):
    #     print(f"{i}: {mod}")
    # quit()

    for min_ideal_name in [
        "min_2_2_C2_sandwich0",
        "min_2_2_C2_sandwich1",
        "min_2_3_1",
        "min_2_4_1",
        "min_2_5_1",
        "min_3_3_1",
        "min_2_2_1",
    ]:
        print(f"{min_ideal_name=}")
        # min_ideal_name = "min_2_2_1"

        # main_refine(9, min_ideal_name, '[0, 0, 0, 0, 0, 0')
        # quit()

        avoid_for_now = [
            "[0, Z, Z x Z x Z x Z]",
            "[0, Z, Z x Z x Z, Z^6]",
            "[0, Z, Z x Z x Z, Z^7]",
            "[0, Z, Z x Z x Z, Z^8]",
            # '[0, Z, Z^5',
            # "[0, 0, Z x Z x Z, Z^6, Z^12",

            # "[0, 0, Z x Z, Z x Z x Z x Z x C2 x C2, Z^8 x C2 x C2 x C2 x C2",
            # "[0, 0, Z x Z, Z x Z x Z x Z, Z^10",
            # "[0, 0, Z x Z, Z x Z x Z x Z, Z^12",
            # "[0, 0, Z x Z, Z x Z, Z^10",
            # "[0, 0, Z x Z, Z^6, Z^14",
            # "[0, 0, Z x Z, Z^6, Z^18",
            # "[0, 0, Z, Z x Z x Z x Z, Z^16",
            # "[0, 0, Z, Z x Z x Z, Z^10",

            # "[C2, Z, Z x Z x C2, Z x Z x Z x Z",
            # "[0, Z, Z x Z x C2, Z x Z x Z x Z",
            # "[0, Z x Z x Z, Z^6, Z^12",
            # "[0, Z x Z, Z x Z x Z, Z^6",
            # "[0, 0, 0, Z x Z",
            # "[0, Z x Z, Z^6, Z^18]",
            # "[0, Z x Z, Z^8, Z^32]",
            # "[0, Z, Z x Z x Z, Z^12]",
            # "[0, Z x Z, Z x Z x Z x Z x C2 x C2, Z^8 x C2^8, Z^16 x C2^30]",
            # "[0, Z x Z, Z x Z x Z x Z, Z^8, Z^16",
            # "[0, Z x Z, Z^6, Z^16, Z^42]",
            # "[0, Z, Z x Z x C2, Z x Z x Z x Z x C2 x C2 x C2 x C2, Z^8 x C2^15]",
            # "[0, Z, Z x Z x C2, Z^5 x C2 x C2 x C2, Z^13 x C2^8]",
            # "[0, Z, Z x Z x Z, Z^6, Z^12, Z^24",
            # "[0, Z, Z x Z x Z, Z^9, Z^24]",
            # "[0, Z, Z x Z x Z, Z^9, Z^27]",
            # "[0, Z, Z x Z, Z x Z x Z x Z, Z^8, Z^16]"
            # "[0, Z, Z x Z, Z^5, Z^13, Z^34]",
            # "[0, Z, Z x Z, Z^5, Z^13]",
            # "[0, Z, Z x Z, Z^6, Z^18]",
            # "[0, Z, Z x C2, Z x Z x C2 x C2 x C2, Z x Z x Z x Z x C2^11, Z^8 x C2^35]",
        ]

        labels = []
        with open(rf"/mnt/c/Users/Owner/Desktop/monoid_homology/data_by_min_ideal/order10/{min_ideal_name}/groupings.txt") as f:
            for line in f:
                label = line[:line.index(" : ")]
                # labels.append(label)
                if not any(label.startswith(skip) for skip in avoid_for_now):
                    if len(label.split(",")) < MAXDIM:
                        labels.append(label)
                    else:
                        print(f"{label} already long enough")
        print("--- Still to do ---")
        for label in labels:
            print(label)


        for label in labels:
            if len(label.split(",")) >= MAXDIM:
                print(f"{label} already long enough")
                continue
            main_refine(10, min_ideal_name, label)