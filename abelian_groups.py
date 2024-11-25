"""
Künneth Theorem Calculator
    and
Universal Coefficient Theorem Calculator

Written by Dennis Sweeney

Calculate elementary divisors, invariant factors,
direct sums, tensor products, tor, ext, and hom modules
of finitely generate abelian groups.

Use this to implement the Künneth Theorem and
Universal Coefficient Theorem.

Example: Compute the homology of RP^6 x S^2

>>> rp6 = [Z, Zmod(2), trivial, Zmod(2), trivial, Zmod(2), trivial]
>>> s2 = [Z, trivial, Z]
>>> for dim, G in enumerate(product_homology(rp6, s2)):
...     print(f"H_{dim} = {G}")
H_0 = Z
H_1 = C2
H_2 = Z
H_3 = C2 x C2
H_4 = trivial
H_5 = C2 x C2
H_6 = trivial
H_7 = C2
H_8 = trivial

Example: Compute the cohomology of RP^6 with coefficients
in Z or in Z/6Z:

>>> for dim, G in enumerate(cohomology_from_homology(rp6, Z)):
...     print(f"H^{dim}(rp6; Z) = {G}")
H^0(rp6; Z) = Z
H^1(rp6; Z) = trivial
H^2(rp6; Z) = C2
H^3(rp6; Z) = trivial
H^4(rp6; Z) = C2
H^5(rp6; Z) = trivial
H^6(rp6; Z) = C2

>>> for dim, G in enumerate(cohomology_from_homology(rp6, Zmod(6))):
...     print(f"H^{dim}(rp6; C6) = {G}")
H^0(rp6; C6) = C2 x C3
H^1(rp6; C6) = C2
H^2(rp6; C6) = C2
H^3(rp6; C6) = C2
H^4(rp6; C6) = C2
H^5(rp6; C6) = C2
H^6(rp6; C6) = C2

Example: Compute the homology with coefficients in Z/Z6:

>>> for dim, G in enumerate(homology_with_coefficients(rp6, Zmod(6))):
...     print(f"H_{dim}(rp6; C6) = {G}")
H_0(rp6; C6) = C2 x C3
H_1(rp6; C6) = C2
H_2(rp6; C6) = C2
H_3(rp6; C6) = C2
H_4(rp6; C6) = C2
H_5(rp6; C6) = C2
H_6(rp6; C6) = C2
"""

from itertools import zip_longest
from collections import defaultdict
from math import prod

try:
    from sympy import factorint
except ImportError:
    import warnings
    warnings.warn("Sympy not found")
    def factorint(n):
        result = {}
        p = 2
        while p * p <= n:
            if n % p == 0:
                n //= p
                exp = 1
                while n % p == 0:
                    n //= p
                    exp += 1
                result[p] = exp
            p += 1
        if n > 1:
            result[n] = 1
        return result


class FinitelyGeneratedAbelianGroup:
    """A Finitely generated abelian groups G
    is always a direct sums of cyclic groups:

        G = Z/m_1 (+) Z/m_2 (+) ... (+) Z/m_k.

    To construct such a group, pass in m_1, ..., m_k as arguments:

    >>> print(FinitelyGeneratedAbelianGroup(2, 3, 4))
    C4 x C2 x C3

    Infinite cyclic summands can be included as Z = Z/0:

    >>> print(FinitelyGeneratedAbelianGroup(0, 0, 2))
    Z x Z x C2

    By default, FinitelyGeneratedAbelianGroups are listed
    by their elementary divisors: we split the group into
    as many direct summands as possible (perhaps applying the
    Chinese Remainder Theorem).

    >>> FinitelyGeneratedAbelianGroup(10)
    FinitelyGeneratedAbelianGroup(2, 5)
    >>> FinitelyGeneratedAbelianGroup(12, 60)
    FinitelyGeneratedAbelianGroup(4, 4, 3, 3, 5)
    >>> print(FinitelyGeneratedAbelianGroup(100))
    C4 x C25

    To recombine the summands into as few direct sums as possible,
    we can find the invariant factors:

    >>> G = FinitelyGeneratedAbelianGroup(0, 0, 2, 4, 8, 3, 9, 5)
    >>> G.invariant_factors()
    [0, 0, 360, 12, 2]
    >>> G.elementary_divisors()
    [0, 0, 8, 4, 2, 9, 3, 5]

    Direct sums concatenate the direct summands:
    
    >>> Z_C4 = FinitelyGeneratedAbelianGroup(0, 4)
    >>> Z_Z_C3 = FinitelyGeneratedAbelianGroup(0, 0, 3)
    >>> print(Z_C4.direct_sum(Z_Z_C3))
    Z x Z x Z x C4 x C3

    Other available operations include tensor products,
    the abelian group hom(G1, G2) of functions
    between two abelian groups under pointwise addition,
    along with Tor and Ext functors.

    >>> Z_C4 = FinitelyGeneratedAbelianGroup(0, 4)
    >>> print(Z_C4.tensor(Z_C4))
    Z x C4 x C4 x C4
    >>> print(Z_C4.tor(Z_C4))
    C4
    >>> print(Z_C4.hom(Z_C4))
    Z x C4 x C4
    >>> print(Z_C4.ext(Z_C4))
    C4 x C4

    The name "Zmod" is an alias for FinitelyGeneratedAbelianGroup.
    The name "Z" is an alias for Zmod(0).
    The name "trivial" is an alias for Zmod().
    """
    # elementary_divisor_prime_exponents is a dict
    # that maps a prime p to a tuple of exponents e
    # for which there is an elementary divisor of
    # the form Z/p**e, with multiplicity.
    # The tuples are in decreasing order.
    # free_rank is an integer.

    # One might improve performance for huge sets of generators
    # by using a collections.Counter instead of a lists/tuples,
    # but I haven't bothered.
    __slots__ = ("_ed_prime_exponents", "free_rank")

    def __new__(cls, *divisors):
        ed = defaultdict(list)
        rank = 0
        for d in divisors:
            d = abs(d)
            if d == 0:
                rank += 1
            elif d == 1:
                pass
            else:
                # Do all the factorization here.
                # After this, work only with primes and exponents.
                for p, e in factorint(d).items():
                    ed[int(p)].append(int(e))
        return cls._from_data(ed, rank)

    @classmethod
    def _from_data(cls, ed_prime_exponents, free_rank):
        obj = object.__new__(cls)
        # Make sure everything is in a predictable order
        obj._ed_prime_exponents = {
            p: tuple(sorted(e_list, reverse=True))
            for p, e_list in sorted(ed_prime_exponents.items())
            if e_list
        }
        obj.free_rank = free_rank
        return obj

    def __eq__(self, other):
        """
        >>> Zmod(2, 3) == Zmod(6)
        True
        >>> Zmod(2, 4) == Zmod(8)
        False
        """
        if not isinstance(other, __class__):
            return NotImplemented
        return (self._ed_prime_exponents == other._ed_prime_exponents
                and self.free_rank == other.free_rank)

    def __hash__(self):
        """
        >>> hash(Zmod(2,3)) == hash(Zmod(3,2)) == hash(Zmod(6))
        True
        >>> hash(Zmod(2,3,0)) == hash(Zmod(2,3))
        False
        """
        return hash((tuple(self._ed_prime_exponents.items()), self.free_rank))

    def elementary_divisors(self):
        """
        >>> Zmod(0, 30, 4).elementary_divisors()
        [0, 4, 2, 3, 5]
        """
        result = [0] * self.free_rank
        for p, e_list in self._ed_prime_exponents.items():
            for e in e_list:
                result.append(p**e)
        return result

    def invariant_factors(self):
        """
        >>> Zmod(0, 30, 4).invariant_factors()
        [0, 60, 2]
        """
        result = [0] * self.free_rank
        torsion = zip_longest(*[
            [p**e for e in e_list]
            for p, e_list in self._ed_prime_exponents.items()
        ], fillvalue=1)
        for p_component_tup in torsion:
            result.append(prod(p_component_tup))
        return result

    def __repr__(self):
        ed_str = ", ".join(map(str, self.elementary_divisors()))
        return f"{type(self).__qualname__}({ed_str})"

    def __str__(self):
        """
        >>> print(Zmod(0,1,2,3,4))
        Z x C4 x C2 x C3
        """
        factors = []
        for d in self.elementary_divisors():
            factors.append("Z" if d == 0 else f"C{d}")
        if not factors:
            return "trivial"
        return " x ".join(factors)
    
    def sage_string(self):
        from collections import Counter
        segments = []
        for d, count in sorted(Counter(self.invariant_factors()).items()):
            base = f"C{d}" if d > 0 else "Z"
            if count > 4:
                res = f"{base}^{count}"
            else:
                res = " x ".join([base]*count)
            segments.append(res)
        if not segments:
            return "0"
        else:
            return " x ".join(segments)


    @classmethod
    def from_string(cls, s):
        """
        >>> Zmod.from_string("C12 x Z x Z^2 x C40")
        FinitelyGeneratedAbelianGroup(0, 0, 0, 8, 4, 3, 5)
        """
        divisors = []
        for summand in s.split("x"):
            summand = summand.strip()
            summand, caret, multiplicity = summand.strip().partition("^")
            multiplicity = int(multiplicity) if multiplicity else 1
            if multiplicity < 0:
                raise ValueError
            summand = summand.strip()
            if summand == "Z":
                d = 0
            elif summand.startswith("C"):
                d = int(summand.removeprefix("C"))
            else:
                raise ValueError(f"Couldn't parse {summand!r}")
            divisors.extend([d] * multiplicity)
        return cls(*divisors)

    def free_part(self):
        """
        >>> print(Zmod(2, 3, 0, 0).free_part())
        Z x Z
        """
        return type(self)._from_data({}, self.free_rank)
    
    def torsion_part(self):
        """
        >>> print(Zmod(2, 3, 0, 0).torsion_part())
        C2 x C3
        """
        return type(self)._from_data(self._ed_prime_exponents, 0)

    def direct_sum(*summands):
        """
        >>> Zmod(2).direct_sum(Zmod(15)) == Zmod(30)
        True
        >>> Zmod(2).direct_sum(Zmod(20)) == Zmod(40)
        False
        """
        # Just collect together the direct summands of each
        primes = set()
        for G in summands:
            primes |= G._ed_prime_exponents.keys()
        new_ed_prime_exponents = {}
        for p in primes:
            new_e_list = []
            for G in summands:
                new_e_list.extend(G._ed_prime_exponents.get(p, ()))
            new_ed_prime_exponents[p] = new_e_list
        r = sum(G.free_rank for G in summands)
        return __class__._from_data(new_ed_prime_exponents, r)

    def tor(self, other):
        """
        >>> print(Zmod(0, 0, 0, 9).tor(Zmod(0, 0, 0, 27)))
        C9
        >>> print(Zmod(30).tor(Zmod(50)))
        C2 x C5
        """
        # Since Tor distributes across direct sums and Tor(Z, anything) = 0
        # and Tor(Z/a, Z/b) = Z/gcd(a,b), we can work one prime at a time.
        primes = self._ed_prime_exponents.keys() & other._ed_prime_exponents.keys()
        new_ed_prime_exponents = {}
        for p in primes:
            e1_list = self._ed_prime_exponents.get(p, ())
            e2_list = other._ed_prime_exponents.get(p, ())
            # gcd(p**e1, p**e2) == p**min(e1, e2), so
            # Tor(Z/p**e1, Z/p**e2) should be Z/p**min(e1, e2)
            new_e_list = [min(e1, e2) for e1 in e1_list for e2 in e2_list]
            new_ed_prime_exponents[p] = new_e_list
        return type(self)._from_data(new_ed_prime_exponents, 0)

    def tensor(self, other):
        """
        >>> print(Zmod(15).tensor(Zmod(10)))
        C5
        >>> print(Zmod(0, 0).tensor(Zmod(0, 0, 0)))
        Z x Z x Z x Z x Z x Z
        >>> print(Zmod(0, 3).tensor(Zmod(0, 5)))
        Z x C3 x C5
        """
        # Since tensor distributes across direct sums
        # and tensor(Z/a, Z/b) = Z/gcd(a,b), we can work one prime at a time.
        # Unlike Tor, we also need to consider the free part.
        primes = self._ed_prime_exponents.keys() | other._ed_prime_exponents.keys()
        new_ed_prime_exponents = {}
        for p in primes:
            e1_list = self._ed_prime_exponents.get(p, ())
            e2_list = other._ed_prime_exponents.get(p, ())
            # gcd(p**e1, p**e2) = p**min(e1, e2), so
            # Z/p**e1 tensor Z/p**e2 should be Z/p**min(e1, e2)
            new_e_list = [min(e1, e2) for e1 in e1_list for e2 in e2_list]
            # Z/p**e1 tensor Z should be Z/p**e1
            new_e_list.extend(e1_list * other.free_rank)
            # Z tensor Z/p**e2 should be Z/p**e2
            new_e_list.extend(e2_list * self.free_rank)
            new_ed_prime_exponents[p] = new_e_list
        r = self.free_rank * other.free_rank
        return type(self)._from_data(new_ed_prime_exponents, r)

    def ext(self, other):
        """
        >>> print(Z.ext(Zmod(2,3,4,5,6,7)))
        trivial
        >>> print(Zmod(2).ext(Z))
        C2
        >>> print(Zmod(12).ext(Zmod(18)))
        C2 x C3
        """
        # Since Ext distributes across (finite!) direct sums
        # and Ext(Z/a, Z/b) = Z/gcd(a,b), we can work one prime at a time.
        primes = self._ed_prime_exponents.keys() | other._ed_prime_exponents.keys()
        new_ed_prime_exponents = {}
        for p in primes:
            e1_list = self._ed_prime_exponents.get(p, ())
            e2_list = other._ed_prime_exponents.get(p, ())
            # gcd(p**e1, p**e2) = p**min(e1, e2), so
            # Ext(Z/p**e1, Z/p**e2) should be Z/p**min(e1, e2)
            new_e_list = [min(e1, e2) for e1 in e1_list for e2 in e2_list]
            # Ext(Z/p**e1, Z) should be Z/p**e1
            new_e_list.extend(e1_list * other.free_rank)
            # note: Ext(Z, anything) is trivial
            new_ed_prime_exponents[p] = new_e_list
        return type(self)._from_data(new_ed_prime_exponents, 0)

    def hom(self, other):
        """
        >>> print(Z.hom(Zmod(0, 0, 0, 2, 3, 4)))
        Z x Z x Z x C4 x C2 x C3
        >>> print(Zmod(10).hom(Zmod(0, 0, 0)))
        trivial
        >>> print(Zmod(10).hom(Zmod(5, 0, 0)))
        C5
        """
        # Since Hom() distributes across (finite!) direct sums
        # and Hom(Z/a, Z/b) = Z/gcd(a, b), we can work one prime at a time.
        primes = self._ed_prime_exponents.keys() | other._ed_prime_exponents.keys()
        new_ed_prime_exponents = {}
        for p in primes:
            e1_list = self._ed_prime_exponents.get(p, ())
            e2_list = other._ed_prime_exponents.get(p, ())
            # gcd(p**e1, p**e2) = p**min(e1, e2), so
            # Hom(Z/p**e1, Z/p**e2) should be Z/p**min(e1, e2)
            new_e_list = [min(e1, e2) for e1 in e1_list for e2 in e2_list]
            # note: Hom(Z/p**e1, Z) is trivial
            # Hom(Z, Z/p**e2) should be Z/p**e2
            new_e_list.extend(e2_list * self.free_rank)
            new_ed_prime_exponents[p] = new_e_list
        r = self.free_rank * other.free_rank
        return type(self)._from_data(new_ed_prime_exponents, r)


Zmod = FinitelyGeneratedAbelianGroup
Z = FinitelyGeneratedAbelianGroup(0)
trivial = FinitelyGeneratedAbelianGroup()


def product_homology(
        homology_list_a : list[FinitelyGeneratedAbelianGroup],
        homology_list_b : list[FinitelyGeneratedAbelianGroup]
        ) -> list[FinitelyGeneratedAbelianGroup]:
    # See Hatcher's Algebraic Topology Book, Theorem 3B.6.
    len_a, len_b = len(homology_list_a), len(homology_list_b)
    result = []
    for dim in range(len_a + len_b - 1):
        summands = []
        for i in range(dim + 1):
            j = dim - i
            if i < len_a and j < len_b:
                ha = homology_list_a[i]
                hb = homology_list_b[j]
                summands.append(ha.tensor(hb))
        for i in range(dim):
            j = dim - 1 - i
            if i < len_a and j < len_b:
                ha = homology_list_a[i]
                hb = homology_list_b[j]
                summands.append(ha.tor(hb))
        result.append(FinitelyGeneratedAbelianGroup.direct_sum(*summands))
    return result


def cohomology_from_homology(homology_list, coefficients):
    # See Hatcher's Algebraic Topology Book, Theorem 3.2.
    G = coefficients
    len_list = len(homology_list)
    result = [homology_list[0].hom(G)]
    for dim in range(1, len_list):
        hdim, lower = homology_list[dim], homology_list[dim - 1]
        result.append(lower.ext(G).direct_sum(hdim.hom(G)))
    return result


def homology_with_coefficients(homology_list, coefficients):
    # See Hatcher's Algebraic Topology book, Corollary 3A.4.
    G = coefficients
    len_list = len(homology_list)
    result = [homology_list[0].tensor(G)]
    for dim in range(1, len_list):
        hdim, lower = homology_list[dim], homology_list[dim - 1]
        result.append(hdim.tensor(G).direct_sum(lower.tor(G)))
    return result


if __name__ == "__main__":
    # C2 = Zmod(2)
    # C4 = Zmod(4)
    # trivial
    # BC2 = [Z] + [C2, trivial] * 20
    # BC4 = [Z] + [C4, trivial] * 20

    # # BC2_C2_C2 = product_homology(product_homology(BC2, BC2), BC2)
    # # for dim, G in enumerate(BC2_C2_C2):
    # #     print(f"H_{dim} = {G}")

    # BC2_C4 = product_homology(BC2, BC4)
    # for dim, G in enumerate(BC2_C4):
    #     print(f"H_{dim} = {G}")

    coeff = 4
    for dim, G in enumerate(homology_with_coefficients([Z, Zmod(2), trivial, trivial], Zmod(coeff))):
        print(f"H_{dim}(rp2;C{coeff}) = {G}")

    # rp2 = [Z, Zmod(2), trivial, trivial, trivial]
    # for dim, G in enumerate(homology_with_coefficients(rp2, Zmod(4))):
    #     print(f"H_{dim}(rp2;C4) = {G}")
    # print()
    # for dim, G in enumerate(cohomology_from_homology(rp2, Zmod(4))):
    #     print(f"H^{dim}(rp2;C4) = {G}")

    # print()
    # klein = [Z, Zmod(0, 2), trivial, trivial, trivial]
    # for dim, G in enumerate(homology_with_coefficients(klein, Zmod(4))):
    #     print(f"H_{dim}(klein;C4) = {G}")

    # print()
    # for dim, G in enumerate(cohomology_from_homology(klein, Zmod(4))):
    #     print(f"H^{dim}(klein;C4) = {G}")
    

    # for dim, G in enumerate(homology_with_coefficients([trivial, trivial, trivial, Zmod(2), trivial, trivial, trivial], Zmod(2))):
    #     print(f"H_{dim}(-;C2) = {G}")

    # import doctest
    # doctest.testmod()
