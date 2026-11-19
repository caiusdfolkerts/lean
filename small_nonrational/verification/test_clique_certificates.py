"""Compare the untrusted producer against exhaustive independent small graphs."""

from itertools import combinations
import random
import unittest

from generate_clique_certificates import emit_certificate, search


def exhaustive(rows, kinds, quota):
    for mask in range(1 << len(rows)):
        vertices = [i for i in range(len(rows)) if mask & (1 << i)]
        if any(sum(kinds[i] == key for i in vertices) < q for key, q in enumerate(quota)):
            continue
        if all(rows[a] & (1 << b) for a, b in combinations(vertices, 2)):
            return True
    return False


class ProducerTests(unittest.TestCase):
    def test_odd_cycle_requires_branch(self):
        rows = [sum(1 << j for j in range(5) if (i - j) % 5 in (1, 4)) for i in range(5)]
        result = search(rows, [0] * 5, (3,), seconds=10)
        self.assertEqual(result["status"], "excluded")
        self.assertTrue(any(node[0] == "split" for node in result["nodes"]))

    def test_separate_kind_quotas(self):
        # Both kind classes have a 2-clique, but no mixed 3-clique exists.
        rows = [0b0110, 0b1001, 0b1001, 0b0110]
        result = search(rows, [0, 0, 1, 1], (2, 1), seconds=10)
        self.assertEqual(result["status"], "excluded")
        self.assertTrue(any(node[0] == "split" for node in result["nodes"]))

    def test_random_graphs_against_exhaustion(self):
        rng = random.Random(176219)
        for _ in range(120):
            size = rng.randrange(1, 9)
            rows = [0] * size
            for a, b in combinations(range(size), 2):
                if rng.randrange(2):
                    rows[a] |= 1 << b
                    rows[b] |= 1 << a
            kinds = [rng.randrange(3) for _ in range(size)]
            quota = tuple(rng.randrange(3) for _ in range(3))
            expected = exhaustive(rows, kinds, quota)
            result = search(rows, kinds, quota, limit=10000, seconds=10)
            self.assertEqual(result["status"], "witness" if expected else "excluded")
            if expected:
                witness = result["witness"]
                self.assertEqual(len(witness), len(set(witness)))
                self.assertTrue(all(rows[a] & (1 << b) for a, b in combinations(witness, 2)))
                self.assertTrue(all(sum(kinds[i] == key for i in witness) >= q
                                    for key, q in enumerate(quota)))

    def test_budget_is_not_an_exclusion(self):
        rows = [sum(1 << j for j in range(5) if (i - j) % 5 in (1, 4)) for i in range(5)]
        result = search(rows, [0] * 5, (3,), limit=1, seconds=10)
        self.assertEqual(result["status"], "budget")
        self.assertIsNone(result["root"])
        self.assertEqual(result["nodes"], [])

    def test_invalid_relation_is_rejected(self):
        with self.assertRaises(ValueError):
            search([2, 0], [0, 0], (1,))
        with self.assertRaises(ValueError):
            search([1], [0], (1,))

    def test_cyclic_certificate_is_rejected(self):
        with self.assertRaises(ValueError):
            emit_certificate([("split", 0, 0, 0)], 0)


if __name__ == "__main__":
    unittest.main()
