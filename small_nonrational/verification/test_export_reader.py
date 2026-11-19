"""The extraction optimization keeps every exact comparison and resource cap."""
from pathlib import Path
import tempfile
import unittest

import export_dependencies as exporter


class ComparisonBatchTests(unittest.TestCase):
    def make_artifacts(self, directory, names, size=100):
        result = {}
        for name in names:
            base = Path(directory) / f"{name}.olean"
            base.write_bytes(b"x" * size)
            Path(str(base) + ".server").write_bytes(b"s" * 10)
            Path(str(base) + ".private").write_bytes(b"p" * 40)
            result[name] = base
        return result

    def test_shared_owner_batches_keep_all_checks_in_order(self):
        with tempfile.TemporaryDirectory() as directory:
            bases = self.make_artifacts(directory, ["A", *map(str, range(7))])
            comparisons = [("A", str(i), ["common", f"another{i}"]) for i in range(7)]
            batches = list(exporter.comparison_batches(comparisons, bases, 4, 100000))
            self.assertEqual([len(batch) for batch, _, _ in batches], [3, 3, 1])
            self.assertEqual([entry for batch, _, _ in batches for entry in batch], comparisons)
            self.assertEqual([mapped for _, _, mapped in batches], [600, 600, 300])
            for batch, modules, mapped in batches:
                self.assertEqual(set(modules), {name for a, b, _ in batch for name in (a, b)})
                self.assertEqual(len(modules), len(set(modules)))
                self.assertEqual(mapped, len(modules) * 150)

    def test_byte_limit_counts_each_input_once(self):
        with tempfile.TemporaryDirectory() as directory:
            bases = self.make_artifacts(directory, "ABCDE")
            comparisons = [("A", "B", ["t"]), ("A", "C", ["t"]), ("D", "E", ["u"])]
            batches = list(exporter.comparison_batches(comparisons, bases, 64, 450))
            self.assertEqual([len(batch) for batch, _, _ in batches], [2, 1])
            self.assertEqual([size for _, _, size in batches], [450, 300])

    def test_disjoint_pairs_respect_module_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            bases = self.make_artifacts(directory, "ABCD")
            comparisons = [("A", "B", ["t"]), ("C", "D", ["u"])]
            self.assertEqual(len(list(exporter.comparison_batches(comparisons, bases, 3, 10000))), 2)
            self.assertEqual(len(list(exporter.comparison_batches(comparisons, bases, 4, 10000))), 1)

    def test_oversized_pair_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            bases = self.make_artifacts(directory, "AB")
            with self.assertRaisesRegex(RuntimeError, "exceeds"):
                list(exporter.comparison_batches([("A", "B", ["t"])], bases, 64, 299))
            with self.assertRaisesRegex(RuntimeError, "exceeds --batch-modules"):
                list(exporter.comparison_batches([("A", "B", ["t"])], bases, 1, 10000))

    def test_invalid_comparisons_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            bases = self.make_artifacts(directory, "AB")
            for comparison in (("A", "A", ["t"]), ("A", "B", []), ("A", "B", ["t", "t"])):
                with self.subTest(comparison=comparison), self.assertRaises(RuntimeError):
                    list(exporter.comparison_batches([comparison], bases, 64, 10000))

    def test_empty_input_and_invalid_limits(self):
        self.assertEqual(list(exporter.comparison_batches([], {}, 1, 1)), [])
        for modules, size in ((0, 100), (2, 0)):
            with self.assertRaises(ValueError):
                list(exporter.comparison_batches([], {}, modules, size))


if __name__ == "__main__":
    unittest.main()
