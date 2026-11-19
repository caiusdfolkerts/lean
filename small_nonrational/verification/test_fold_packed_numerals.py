#!/usr/bin/env python3
"""Regression checks for exact certificate-data constant folding."""
import random
import unittest

import fold_packed_numerals as fold


class PackedNumeralFoldingTests(unittest.TestCase):
    def test_generated_trees_keep_the_same_integer(self):
        rng = random.Random(20261119)

        def tree(depth):
            if depth == 0 or rng.randrange(3) == 0:
                value = rng.getrandbits(rng.randrange(0, 500))
                return hex(value), value, 0
            left, a, na = tree(depth - 1)
            if rng.randrange(2):
                right, b, nb = tree(depth - 1)
                return f"(Nat.lor {left} {right})", a | b, na + nb + 1
            amount = rng.randrange(0, 1000)
            return f"(Nat.shiftLeft {left} {amount})", a << amount, na + 1

        for _ in range(300):
            source, value, operations = tree(8)
            with self.subTest(source=source[:120]):
                got, end, count = fold.parse_closed_nat(source, 0)
                self.assertEqual((got, end, count), (value, len(source), operations))

    def test_deep_trees_do_not_require_python_recursion(self):
        source = "(Nat.lor 1 " * 4000 + "0" + ")" * 4000
        self.assertEqual(fold.parse_closed_nat(source, 0), (1, len(source), 4000))

    def test_rejects_nonclosed_expressions(self):
        for source in ("(Nat.lor x 2)", "(Nat.lor 1 2 3)",
                       "(Nat.shiftLeft 1 -2)", "(Nat.add 1 2)",
                       "(Nat.lor 1)", "(Nat.lor 0xgg 1)",
                       "(Nat.lor 1 2", "(Nat.lor 1 2abc)"):
            with self.subTest(source=source), self.assertRaises(fold.NotClosedNumeral):
                fold.parse_closed_nat(source, 0)

    def test_size_gate_rejects_expanding_shift(self):
        with self.assertRaises(fold.NotClosedNumeral):
            fold.parse_closed_nat("(Nat.shiftLeft 1 100000000000)", 0)

    def test_no_edits_in_comments_or_strings(self):
        source = '''module
prelude
-- (Nat.lor 1 2)
/- (Nat.lor 4 8) /- nested -/ more -/
def text := "a \\\" (Nat.lor 16 32)"
def data : Nat := (Nat.lor 64 (Nat.shiftLeft 3 8))
'''
        changed, rows = fold.fold_source(source, minimum_chars=1)
        self.assertEqual(len(rows), 1)
        self.assertIn('def data : Nat := hexnat% "340"', changed)
        self.assertIn('-- (Nat.lor 1 2)', changed)
        self.assertIn('"a \\\" (Nat.lor 16 32)"', changed)
        self.assertEqual(changed.count(fold.META_IMPORT), 1)
        self.assertEqual(fold.fold_source(changed, minimum_chars=1), (changed, []))

    def test_keeps_existing_meta_import_once(self):
        source = "module\npublic meta import HexNatLiteral\ndef x : Nat := (Nat.lor 1 2)\n"
        changed, rows = fold.fold_source(source, minimum_chars=1)
        self.assertEqual(changed.count(fold.META_IMPORT), 1)
        self.assertEqual(len(rows), 1)

    def test_no_edits_in_raw_strings_or_quoted_identifiers(self):
        source = '''module
def «(Nat.lor 1 2) -- not a comment» : Nat := 0
def raw := r##"quote " (Nat.lor 4 8) /- not a comment -/"##
def plainRaw := r"(Nat.lor 16 32)"
def data : Nat := (Nat.lor 64 128)
'''
        changed, rows = fold.fold_source(source, minimum_chars=1)
        self.assertEqual(len(rows), 1)
        self.assertIn('def data : Nat := hexnat% "c0"', changed)
        self.assertIn('«(Nat.lor 1 2) -- not a comment»', changed)
        self.assertIn('r##"quote " (Nat.lor 4 8) /- not a comment -/"##', changed)
        self.assertIn('r"(Nat.lor 16 32)"', changed)

    def test_literal_formats_and_zero(self):
        self.assertEqual(fold.parse_closed_nat("(Nat.lor 0X_fF 1_024)", 0)[0], 1279)
        self.assertEqual(fold.parse_closed_nat("(Nat.shiftLeft 0 1000)", 0)[0], 0)

    def test_unsupported_source_header_fails(self):
        with self.assertRaises(fold.NotClosedNumeral):
            fold.fold_source("def x := (Nat.lor 1 2)", minimum_chars=1)

    def test_incomplete_comments_or_strings_fail(self):
        for source in ('module\n/- unterminated', 'module\n"unterminated',
                       'module\n«unterminated', 'module\nr##"unterminated"#'):
            with self.subTest(source=source), self.assertRaises(fold.NotClosedNumeral):
                fold.fold_source(source)


if __name__ == "__main__":
    unittest.main()
