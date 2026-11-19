"""Safety checks for replacing a selected case without retaining its old replay."""
import unittest
from pathlib import Path

from install_graph_replacements import (RETIRED_NODE_FIELDS, merge_sources, remove_checked_records,
                                        replace_case, retire_node_payload, refresh_local_checks)


class ReplacementTests(unittest.TestCase):
    def test_only_selected_checked_block_is_removed(self):
        source = '''module
prelude
public import ExampleData
namespace Example
theorem record000_nodes_0 : True := by trivial
theorem record000_checked : True := record000_nodes_0
#print axioms record000_checked
theorem record001_nodes_0 : True := by trivial
#print axioms record001_nodes_0
end Example
'''
        result = remove_checked_records(source, {'record000'})
        self.assertNotIn('record000', result)
        self.assertIn('record001_nodes_0', result)
        self.assertEqual(remove_checked_records(result, {'record000'}), result)

    def test_dangling_reference_is_rejected(self):
        source = 'theorem record000_checked : True := by trivial\n'
        source += 'theorem record001_checked : True := record000_checked\n'
        with self.assertRaises(ValueError):
            remove_checked_records(source, {'record000'})

    def test_case_result_and_numerical_parameters_are_preserved(self):
        source = '''theorem record000_core : Core record000 where
  nodes := record000_raw_node_checks record000_validity
theorem record000_parameters : Parameters record000 row 123 := parameters
theorem record000_result : Result (29, 123) :=
  of_small 29 123 (by decide) ⟨record000, record000_core, record000_parameters, record000_coverage⟩
#print axioms record000_result
'''
        result = replace_case(source, 'record000', 'Example.Fast', 29)
        self.assertNotIn('record000_core', result)
        self.assertIn('theorem record000_result : Result (29, 123)', result)
        self.assertIn('record000_parameters : Parameters record000 row 123', result)
        self.assertIn('of_direct_small 29 123', result)
        self.assertIn('Example.Fast.direct_core', result)
        self.assertEqual(replace_case(result, 'record000', 'Example.Fast', 29), result)

    def test_module_merging_deduplicates_only_headers(self):
        left = 'module\nprelude\npublic import Common\n@[expose] public section\nnamespace A\nend A\n'
        right = 'module\nprelude\npublic import Common\npublic meta import Builder\n@[expose] public section\nnamespace B\nend B\n'
        source = merge_sources([left, right])
        self.assertEqual(source.count('public import Common'), 1)
        self.assertIn('public meta import Builder', source)
        self.assertIn('namespace A', source)
        self.assertIn('namespace B', source)

    def test_retired_payload_preserves_every_geometric_field(self):
        original = {key: '123456' for key in RETIRED_NODE_FIELDS}
        original.update(cells='⟨17, 987654321⟩', leaves='⟨8, 12345⟩', quota='⟨4, 2345⟩',
                        candidateMatrix='99293', cellMaps='66554', embedding='⟨3, 7654321⟩')
        source = 'namespace Example\ndef record000 : RawData := {\n' + ''.join(
            f'  {name} := {value}\n' for name, value in original.items()) + '}\nend Example\n'
        result = retire_node_payload(Path('Example.lean'), source, {'record000'})
        for name, value in original.items():
            if name not in RETIRED_NODE_FIELDS:
                self.assertIn(f'  {name} := {value}', result)
        self.assertIn('  nodePred := 0', result)
        self.assertIn('  nodeCodes := ⟨1, 0⟩', result)
        self.assertEqual(retire_node_payload(Path('Example.lean'), result, {'record000'}), result)

    def test_local_cache_alias_is_replaced_by_an_actual_check(self):
        source = '''theorem record000_local_0 : Interval (localCheck record000) 64 99 :=
  Earlier.record100_local_checked
theorem record001_local_checked : Interval (localCheck record001) 0 70 :=
  Earlier.record200_local_checked
'''
        result = refresh_local_checks(source, {'record000'})
        self.assertIn('interval_of_check _ 64 35 (by decide +kernel)', result)
        self.assertNotIn('Earlier.record100_local_checked', result)
        self.assertIn('Earlier.record200_local_checked', result)


if __name__ == '__main__':
    unittest.main()
