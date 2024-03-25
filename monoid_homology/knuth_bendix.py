"""
Apply the Knuth-Bendix algorithm for monoid presentations.

Given an input list of pair of strings that are declared equal,
produce an output list of such pairs of strings so that
two strings are equal according to the input list
iff they are equal according to the output list.

Example:

    >>> kb_normalize([('xxx', ''), ('yyy', ''), ('xyxyxy', '')])
    [('xxx', ''), ('yyy', ''), ('yyxx', 'xyxy'), ('yxyx', 'xxyy')]

The output list is normalized so that applying
`word = word.replace(left, right)` for each `(left, right)` pair
repeatedly in any order will eventually terminate, and will
always reach the same fully-reduced final answer regardless of the
order in which the rules are applied.
Thus, the word problem for the monoid is solved: two strings
are equal if and only if they reduce to the same word.

The input list in the example is not normalized because
starting with xxxyxyxy, we can use the input list of replacements
to produce yxyxy, which is then irreducible by the input list,
while we could also have used a different rule to produce xx,
which is likewise irreducible; order mattered.
"""

__all__ = ["normalize"]

from collections import defaultdict

def reduced(word, rule_list):
    # This is only called when rule_list has shortlex-shrinking words
    while True:
        word0 = word
        for left, right in rule_list:
            word = word.replace(left, right)
        if word == word0:
            return word

def shortlex_ordered(a: str, b: str):
    if (len(a), a) > (len(b), b):
        return (a, b)
    else:
        return (b, a)

def kb_complete(rules, *, iteration_limit=20, verbose=False):
    # copy to verify at the end
    rules0 = [(left, right) for left, right in rules]

    # make rules strictly decrease the shortlex. maintain this.
    rule_set = set()
    for left, right in rules0:
        if left != right:
            rule_set.add(shortlex_ordered(left, right))

    # for all i <= j < rule_list_num_reduced,
    # rule_list[i] and rule_list[j] do not reduce each other.
    rule_list = sorted(rule_set)
    rule_list_num_reduced = 0

    def replace_rule_at_index(i, new1, new2):
        rule_set.remove(rule_list[i])
        del rule_list[i]
        nonlocal rule_list_num_reduced
        if i < rule_list_num_reduced:
            rule_list_num_reduced -= 1
        left, right = new_rule = shortlex_ordered(new1, new2)
        if left != right and new_rule not in rule_set:
            rule_set.add(new_rule)
            rule_list.append(new_rule)

    iteration = 0
    while True:
        iteration += 1
        if iteration_limit is not None and iteration > iteration_limit:
            raise RuntimeError(f"Did not normalize after {iteration_limit} loops")

        # Phase 1: normalization
        # Ensure that no right-hand sides contain left-hand sides
        # Also ensure that no left-hand sides contain other left-hand sides.
        if verbose:
            print(f"rule_list={rule_list}")
        while rule_list_num_reduced < len(rule_list):
            rule1 = rule_list[rule_list_num_reduced]
            left1, right1 = rule1
            for i, rule2 in enumerate(rule_list[:rule_list_num_reduced+1]):
                left2, right2 = rule2
                if left2 in right1:
                    # replace rule1
                    replace_rule_at_index(rule_list_num_reduced, right1.replace(left2, right2), left1)
                    if verbose:
                        print(f"reducing {rule1} via {rule2}")
                        print(f"rule_list={rule_list}")
                    break
                if left1 in right2:
                    # replace rule2
                    replace_rule_at_index(i, right2.replace(left1, right1), left2)
                    if verbose:
                        print(f"reducing {rule2} via {rule1}")
                        print(f"rule_list={rule_list}")
                    break
                if i == rule_list_num_reduced:
                    # left side will always contain itself; that's okay.
                    continue
                if left2 in left1:
                    # replace rule1
                    replace_rule_at_index(rule_list_num_reduced, left1.replace(left2, right2), right1)
                    if verbose:
                        print(f"reducing {rule1} via {rule2}")
                        print(f"rule_list={rule_list}")
                    break
                if left1 in left2:
                    # replace rule2
                    replace_rule_at_index(i, left2.replace(left1, right1), right2)
                    if verbose:
                        print(f"reducing {rule2} via {rule1}")
                        print(f"rule_list={rule_list}")
                    break
            else:
                # no break: no reductions made
                rule_list_num_reduced += 1

        # Phase 2: finding critical pairs
        # Since we've normalized the rules, only consider
        # (AB-->..., BC-->...) cases, not (ABC-->...,B-->...) cases.

        prefix_to_rules = defaultdict(list)
        suffix_to_rules = defaultdict(list)
        for rule in rule_list:
            left, right = rule
            for i in range(1, len(left)):
                pre, suf = left[:i], left[i:]
                prefix_to_rules[pre].append(rule)
                suffix_to_rules[suf].append(rule)
        critical_pairs = []
        for aff in prefix_to_rules.keys() & suffix_to_rules.keys():
            assert aff
            for rule_with_prefix in prefix_to_rules[aff]:
                left1, right1 = rule_with_prefix
                assert left1.startswith(aff)
                left1_end = left1[len(aff):]
                assert aff + left1_end == left1
                for rule_with_suffix in suffix_to_rules[aff]:
                    left2, right2 = rule_with_suffix
                    assert left2.endswith(aff)
                    left2_start = left2[:-len(aff)]
                    assert left2_start + aff == left2
                    # left2_start + aff + left1_end
                    # reduces to both:
                    crit1 = reduced(right2 + left1_end, rule_list)
                    crit2 = reduced(left2_start + right1, rule_list)
                    if crit1 != crit2:
                        pair = shortlex_ordered(crit1, crit2)
                        assert pair not in rule_set
                        if verbose:
                            print(f"{(left2_start, aff, left1_end)} did not resolve.")
                            print(f"Adding {pair}")
                        critical_pairs.append(pair)

        if not critical_pairs:
            if verbose:
                print("Found no critical pairs. Success!\n\n")
                print(rule_list)
            break
        for pair in critical_pairs:
            if pair not in rule_set:
                rule_set.add(pair)
                rule_list.append(pair)

    assert set(rule_list) == rule_set
    for left0, right0 in rules0:
        assert reduced(left0, rule_list) == reduced(right0, rule_list)
    return rule_list


def kb_normalize(alphabet, rules0, **kwargs):
    rules = kb_complete(rules0, **kwargs)
    # remove single-letter left-hand sides.
    normal_rules = []
    for rule in rules:
        if len(rule[0]) == 1:
            alphabet = alphabet.replace(rule[0][0], '')
        else:
            normal_rules.append(rule)
    return (alphabet, normal_rules)