from monoid_homology.by_min_ideal import (
    get_min_names,
    iterate_from_size_and_min_name,
    subset_from_size_and_min_name,
    one_op_from_size_and_min_name,
    get_count_from_size_and_min_name,
)
import random

def test_get_min_names():
    assert get_min_names(4) == ["min_2_2_1"]
    assert get_min_names(5) == ["min_2_2_1"]
    assert get_min_names(6) == ["min_2_2_1", "min_2_3_1"]
    assert get_min_names(7) == ["min_2_2_1", "min_2_3_1"]
    assert get_min_names(8) == ["min_2_2_1", "min_2_2_C2_sandwich0", "min_2_2_C2_sandwich1", "min_2_3_1", "min_2_4_1"]
    assert get_min_names(9) == ["min_2_2_1", "min_2_2_C2_sandwich0", "min_2_2_C2_sandwich1", "min_2_3_1", "min_2_4_1", "min_3_3_1"]
    assert get_min_names(10) == ["min_2_2_1", "min_2_2_C2_sandwich0", "min_2_2_C2_sandwich1", "min_2_3_1", "min_2_4_1", "min_2_5_1", "min_3_3_1"]

def test_get_count_from_size_and_min_name():
    for (n, min_name, count) in [
        (4, "min_2_2_1", 1),
        (5, "min_2_2_1", 4),
        (6, "min_2_2_1", 47),
        (7, "min_2_2_1", 606),
        (8, "min_2_2_1", 10684),
        (8, "min_2_2_C2_sandwich0", 1),
        (8, "min_2_2_C2_sandwich1", 1),
        (8, "min_2_3_1", 178),
        (8, "min_2_4_1", 1),
    ]:
        assert get_count_from_size_and_min_name(n, min_name) == count

def test_data_456():
    for n in (4, 5, 6):
        for min_name in get_min_names(n):
            all_ops = list(iterate_from_size_and_min_name(n, min_name))
            N = len(all_ops)
            all_ops_as_subset = list(subset_from_size_and_min_name(n, min_name, range(N)))
            assert all_ops_as_subset == all_ops

            all_ops_one_by_one = [
                (index, one_op_from_size_and_min_name(n, min_name, index))
                for index in range(N)
            ]
            assert all_ops_one_by_one == all_ops

def test_data_subsets():
    for n in (4, 5, 6, 7, 8, 9, 10):
        for min_name in get_min_names(n):
            N = get_count_from_size_and_min_name(n, min_name)
            indexes = [random.randrange(N) for _ in range(3)]
            ops_as_subset = list(subset_from_size_and_min_name(n, min_name, indexes))
            one_by_one = [
                (index, one_op_from_size_and_min_name(n, min_name, index))
                for index in indexes
            ]
            assert ops_as_subset == one_by_one

