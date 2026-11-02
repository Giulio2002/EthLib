#!/usr/bin/env python3
"""Regression tests for the lexical declaration inventory."""
import unittest

from generate_api_inventory import headers


class HeaderExtractionTests(unittest.TestCase):
    def test_terminal_equation_style(self):
        source = 'namespace Example\ndef settle : Nat → Nat\n  | 0 => 0\n  | n + 1 => n\nend Example\n'
        self.assertEqual(headers(source), {'settle': 'def settle : Nat → Nat'})

    def test_equation_body_does_not_consume_next_declaration(self):
        source = 'def f : Nat → Nat\n  | n => n\n\ndef next : Nat := 1\n'
        self.assertEqual(headers(source), {'f': 'def f : Nat → Nat', 'next': 'def next : Nat'})

    def test_multiline_and_where_headers(self):
        source = 'theorem id\n    (x : Nat) : x = x := by rfl\nstructure Box where\n  value : Nat\n'
        self.assertEqual(headers(source), {'id': 'theorem id (x : Nat) : x = x', 'Box': 'structure Box'})

    def test_missing_delimiter_fails_instead_of_skipping(self):
        with self.assertRaisesRegex(ValueError, 'no header delimiter'):
            headers('def incomplete : Nat\n')

    def test_duplicate_names_fail_instead_of_overwriting(self):
        with self.assertRaisesRegex(ValueError, 'duplicate declaration'):
            headers('def same : Nat := 1\ndef same : Nat := 2\n')


if __name__ == '__main__':
    unittest.main()
