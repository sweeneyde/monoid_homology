# Monoid Homology

This repository computes the homology of [monoids](https://en.wikipedia.org/wiki/Monoid) in SAGE.
The homology of a monoid is the homology of its [nerve](https://en.wikipedia.org/wiki/Nerve_(category_theory)) (classifying space).
[A result of Ken Brown](https://doi.org/10.1007/978-1-4613-9730-4_6)
allows this to be carried out for certain finite monoid presentations, even if the resulting monoid is infinite.

## Example Usage

After cloning this repository, open a SAGE console and write

```sage
sage: sys.path.append(PATH_TO_THIS_REPOSITORY)
sage: from monoid_homology import CRS, kb_normalize
```

From here we can compute some monoid homology. First, the natural numbers
are a monoid with one generator an no relations:

```sage
sage: nat = CRS("x", [])
sage: nat.homology_list(5)
[Z, 0, 0, 0, 0]
```

Classical results for group homology can be quickly replicated (homology is listed starting in dimension 1):

```sage
sage: Z3 = CRS("x", [("xxx", "")])
sage: Z3.homology_list(20)
[C3, 0, C3, 0, C3, 0, C3, 0, C3, 0, C3, 0, C3, 0, C3, 0, C3, 0, C3, 0]

sage: D10 = CRS("rs", [("rrrrr", ""), ("ss", ""), ("rs", "srrrr")])
sage: D10.homology_list(7)
[C2, 0, C10, 0, C2, 0, C10]
```

While the classifying space BG is a K(G,1) when G is a group,
there is no such restriction for monoids: any connected CW complex
can be approximated by a monoid up to homotopy equivalence.
This is a result of Dusa Mcduff.
As an example, we can make a 2-sphere with a finite monoid:

```sage
sage: rectangular_band_2_2 = CRS("xy", [("xx", "x"), ("yy", "y"), ("xyx", "x"), ("yxy", "y")])
sage: rectangular_band_2_2.homology_list(5)
[0, Z, 0, 0, 0]
```

This `CRS` class requires that the entered monoid presentation be a normalized complete rewriting system: any conflicting rules must resolve their conflicts via more rules.
If this is not the case, we can try to convert an arbitrary presentation into a complete rewriting system using the Knuth-Bendix algorithm, though this somtimes might not halt.
Here's an example in which the defining relations of the dihedral group are massaged into a complete rewriting system:

```sage
sage: kb_normalize("rs", [("rrrrr", ""), ("ss", ""), ("rsrs", "")])
('rs',
 [('ss', ''),
  ('rrrr', 'srs'),
  ('rsr', 's'),
  ('srrr', 'rrs'),
  ('rrrs', 'srr'),
  ('srrs', 'rrr')])
```

## Finite Monoid Results

Data taken from GAP's smallsemi package. See the [wiki](https://github.com/sweeneyde/monoid_homology/wiki/Homology-of-semigroups-with-1%E2%80%906-elements) for some homology data of finite monoids.
