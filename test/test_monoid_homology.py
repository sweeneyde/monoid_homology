from monoid_homology import CRS

def test_crs_homology():
    # Uses Sympy because it's hard to set up CI for SAGE.

    trivial = CRS("", [])
    assert trivial.sympy_rational_homology_ranks(4) == [1, 0, 0, 0, 0]

    NxN = CRS("xy", [("yx", "xy")])
    assert NxN.sympy_rational_homology_ranks(3) == [1, 2, 1, 0]

    NxNxN = CRS("xyz", [("yx", "xy"), ("zx", "xz"), ("zy", "yz")])
    assert NxNxN.sympy_rational_homology_ranks(3) == [1, 3, 3, 1]

    Z = CRS("xy", [("xy", ""), ("yx", "")])
    assert Z.sympy_rational_homology_ranks(3) == [1, 1, 0, 0]

    Free2 = CRS("xy", [])
    assert Free2.sympy_rational_homology_ranks(3) == [1, 2, 0, 0]

    Z3 = CRS("x", [("xxx", "")])
    assert Z3.sympy_rational_homology_ranks(3) == [1, 0, 0, 0]

    # Rectangular bands
    rect22 = CRS("xy", [("xx", "x"), ("yy", "y"), ("xyx", "x"), ("yxy", "y")])
    assert rect22.sympy_rational_homology_ranks(4) == [1, 0, 1, 0, 0]

    rect33 = CRS("xyz", [(a+a, a) for a in "xyz"] +
                        [(a+b+a, a) for (a, b) in "xy xz yx yz zx zy".split()] +
                        [(a+b+c, a+c) for (a, b, c) in "xyz xzy yxz yzx zxy zyx".split()])
    assert rect33.sympy_rational_homology_ranks(3) == [1, 0, 4, 0]



def test_crs_essentials():
    rect22 = CRS("xy", [("xx", "x"), ("yy", "y"), ("xyx", "x"), ("yxy", "y")])
    rect22.compute_essentials(3)
    for dim, ess_set in {
        0: {()},
        1: {("x",), ("y",)},
        2: {("x", "x"), ("x", "yx"), ("y", "y"), ("y", "xy")},
        3: {
            ("x", "x", "x"), ("x", "x", "yx"),
            ("y", "y", "y"), ("y", "y", "xy"),
            ("x", "yx", "y"), ("x", "yx", "x"),
            ("y", "xy", "y"), ("y", "xy", "x"),
        }
    }.items():
        assert set(rect22.essentials[dim]) == ess_set

    Z = CRS("xy", [("xy", ""), ("yx", "")])
    Z.compute_essentials(3)
    for dim, ess_set in {
        0: {()},
        1: {("x",), ("y",)},
        2: {("x", "y"), ("y", "x")},
        3: {("x", "y", "x"), ("y", "x", "y")},
    }.items():
        assert set(Z.essentials[dim]) == ess_set