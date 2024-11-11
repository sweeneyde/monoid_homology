import gzip
import io
from pathlib import Path
from functools import lru_cache

def path_from_size_and_min_name(n: int, min_name: str):
    return Path(__file__).parent.parent / "data_by_min_ideal" / f"order{n}" / min_name / "tables.dat.gz"

@lru_cache(maxsize=1)
def _data_from_gz(n, filename):
    with gzip.open(filename, "rb") as f:
        data = f.read().splitlines()
    num = len(data[0])
    assert len(data) == n * n
    for packed in data:
        assert len(packed) == num
    return data

def data_from_size_and_min_name(n, min_name):
    return _data_from_gz(n, path_from_size_and_min_name(n, min_name))

def _iterate_from_gz(n, filename):
    data = _data_from_gz(n, filename)
    num = len(data[0])
    rn = range(n)
    range_num = range(num)
    for index in range_num:
        yield index, [
            [int(data[i*n + j][index:index+1])
             for j in rn
            ]
            for i in rn
        ]

def iterate_from_size_and_min_name(n, min_name):
    return _iterate_from_gz(n, path_from_size_and_min_name(n, min_name))

def _subset_from_gz(n, filename, indexes):
    data = _data_from_gz(n, filename)
    rn = range(n)
    for index in indexes:
        yield index, [
            [int(data[i*n + j][index:index+1])
             for j in rn
            ]
            for i in rn
        ]

def subset_from_size_and_min_name(n, min_name, indexes):
    return _subset_from_gz(n, path_from_size_and_min_name(n, min_name), indexes)

def _one_op_from_gz(n, filename, index):
    with gzip.open(filename, "rb") as f:
        file_size = f.seek(0, io.SEEK_END)
        if file_size % (n * n) != 0:
            raise ValueError
        N = file_size // (n * n)
        if not (0 <= index < N - 1):
            raise ValueError(f"{index} is not in range({N-1})")
        for i in range(n*n):
            f.seek(N*i + N-1)
            if f.read(1) != b'\n':
                raise ValueError
        op = []
        for i in range(n):
            row = []
            for j in range(n):
                f.seek(N * (n * i + j) + index)
                row.append(int(f.read(1)))
            op.append(row)
    return op

def one_op_from_size_and_min_name(n, min_name, index):
    return _one_op_from_gz(n, path_from_size_and_min_name(n, min_name), index)

def get_min_names(n):
    folder = Path(__file__).parent.parent / "data_by_min_ideal" / f"order{n}"
    names = [subfolder.name for subfolder in folder.iterdir() if subfolder.is_dir()]
    names.sort()
    return names

def get_count_from_size_and_min_name(n, min_name):
    folder = Path(__file__).parent.parent / "data_by_min_ideal" / f"order{n}" / min_name
    readme = (folder / "README.md").read_text()
    total = int(readme.partition(" semigroups")[0].partition("Found ")[2])
    return total
