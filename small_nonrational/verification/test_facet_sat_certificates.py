"""Independent semantic checks for the untrusted certificate producer."""
import itertools
import unittest

from generate_facet_sat_certificates import (Formula, encode, incompatible_classes, make_cell,
                                             negate, prune_rup_dependencies, trim)
from generate_clique_certificates import pack
from read_graph_records import leaf_orbits


def interpretation(atoms, selected, kind_vertices, groupings=None):
    values = {}
    for index, atom in enumerate(atoms, start=1):
        if atom['tag'] == 'facet':
            values[index] = selected[atom['index']]
        elif atom['tag'] == 'counter':
            vertices = kind_vertices[atom['kind']][:atom['prefix']]
            values[index] = sum(selected[v] for v in vertices) >= atom['threshold']
        elif atom['tag'] == 'totalizer':
            values[index] = sum(selected[v] for v in atom['vertices']) >= atom['threshold']
        elif atom['tag'] == 'group':
            values[index] = any(selected[v] for v in groupings[atom['kind']][atom['index']])
        elif atom['tag'] == 'group_totalizer':
            values[index] = sum(any(selected[v] for v in groupings[atom['kind']][g])
                                for g in atom['vertices']) >= atom['threshold']
        else:
            raise AssertionError(atom)
    return values


def satisfied(clause, values):
    return any(values[abs(literal)] == (literal > 0) for literal in clause)


class FacetSatProducerTests(unittest.TestCase):
    def test_coloring_and_group_quotas_preserve_all_compatible_selections(self):
        # Test all graphs up to four vertices, not just the producer's examples.
        # Each selected clique may use at most one member of an independent class.
        for size in range(5):
            pairs = list(itertools.combinations(range(size), 2))
            for graph in range(1 << len(pairs)):
                rows = [0] * size
                for index, (a, b) in enumerate(pairs):
                    if graph >> index & 1:
                        rows[a] |= 1 << b
                        rows[b] |= 1 << a
                groups = incompatible_classes(list(range(size)), rows)
                self.assertEqual(sorted(v for group in groups for v in group), list(range(size)))
                self.assertTrue(all(not (rows[a] >> b & 1) for group in groups
                                    for a, b in itertools.combinations(group, 2)))
                cells = [make_cell(i, 1, 1 << i, [], []) for i in range(size)]
                for quota in range(size + 2):
                    formula = Formula(size)
                    formula.grouped_counter(cells, rows, quota, 1, lower_only=False)
                    for selected in itertools.product((False, True), repeat=size):
                        ids = [a for a in range(size) if selected[a]]
                        if any(not (rows[a] >> b & 1) for a, b in itertools.combinations(ids, 2)):
                            continue
                        values = interpretation(formula.atoms, selected, {1: list(range(size))}, {1: groups})
                        self.assertEqual(all(satisfied(clause, values) for clause in formula.clauses),
                                         len(ids) == quota, (size, graph, quota, selected))

    def test_group_indices_are_not_cnf_variable_indices(self):
        formula = Formula(5)
        group_vars = [formula.variable(dict(tag='group', kind=2, index=g)) for g in range(3)]
        formula.totalizer(group_vars, 2, 2, lower_only=False, group_indices=[0, 1, 2])
        atoms = [atom for atom in formula.atoms if atom['tag'] == 'group_totalizer']
        self.assertTrue(atoms)
        self.assertTrue(all(set(atom['vertices']) <= {0, 1, 2} for atom in atoms))
        self.assertTrue(all(rule.get('grouped') for rule in formula.rules))

    def test_cardinality_encodings_have_their_claimed_semantics(self):
        # The auxiliary assignment comes from actual cardinalities, independently
        # of the CNF producer's recurrence and of the external SAT solver.
        for size in range(7):
            for quota in range(size + 2):
                for lower_only in (False, True):
                    for encoding in ('counter', 'totalizer'):
                        formula = Formula(size)
                        getattr(formula, encoding)(list(range(1, size + 1)), quota, 1,
                                                   lower_only=lower_only)
                        for selected in itertools.product((False, True), repeat=size):
                            values = interpretation(formula.atoms, selected, {1: list(range(size))})
                            expected = sum(selected) >= quota if lower_only else sum(selected) == quota
                            actual = all(satisfied(clause, values) for clause in formula.clauses)
                            self.assertEqual(actual, expected,
                                             (encoding, size, quota, lower_only, selected))

    def test_integer_one_is_not_the_boolean_constant_true(self):
        formula = Formula(1)
        formula.add({'tag': 'test'}, 1, False)
        self.assertEqual(formula.clauses, [[1]])
        formula.add({'tag': 'test'}, True, -1)
        self.assertEqual(formula.clauses, [[1]])
        self.assertIs(negate(True), False)
        self.assertEqual(negate(1), -1)

    def test_unused_unit_propagations_are_removed(self):
        clauses = {1: [1], 2: [2], 3: [-1]}
        self.assertEqual(prune_rup_dependencies([], [1, 2, 3], clauses), [1, 3])

    def test_nonunit_or_missing_hints_are_rejected(self):
        for hints, clauses in [([1], {1: [1, 2]}), ([1], {}), ([1], {1: [1]})]:
            with self.assertRaises(ValueError):
                prune_rup_dependencies([], hints, clauses)

    def test_transitive_core_preserves_rule_witnesses(self):
        formula = Formula(3)
        formula.add({'tag': 'left'}, 1)
        formula.add({'tag': 'irrelevant'}, 3)
        formula.add({'tag': 'right'}, -1)
        core = trim(formula, '4 0 1 2 3 0\n')
        self.assertEqual(core['clauses'], [[1], [-1]])
        self.assertEqual([rule['tag'] for rule in core['rules']], ['left', 'right'])
        self.assertEqual(core['lrat'], '3 0 1 2 0\n')

    def test_initial_empty_clause_has_a_uniform_checked_refutation(self):
        formula = Formula(1)
        formula.add({'tag': 'impossible'})
        core = trim(formula, '')
        self.assertEqual(core['clauses'], [[]])
        self.assertEqual(core['lrat'], '2 0 1 0\n')
        self.assertEqual(core['rules'][0]['tag'], 'impossible')

    def test_terminal_blocking_preserves_exact_coverage(self):
        cells = [make_cell(i, 1, 1 << i, [], []) for i in range(3)]
        orbits = [dict(vertices=[0, 1], original_leaf=0, word=[])]
        formula = encode(cells, (0, 2), counter='totalizer', orbits=orbits)
        blocks = [clause for clause, rule in zip(formula.clauses, formula.rules)
                  if rule['tag'] == 'block']
        self.assertEqual(blocks, [[-1, -2]])
        for selected in itertools.product((False, True), repeat=3):
            values = interpretation(formula.atoms, selected, {1: [0, 1, 2]})
            actual = all(satisfied(clause, values) for clause in formula.clauses)
            self.assertEqual(actual, sum(selected) == 2 and selected != (True, True, False))
        with self.assertRaises(ValueError):
            encode(cells, (0, 2), lower_only=True, orbits=orbits)
        with self.assertRaises(ValueError):
            encode(cells, (0, 2), orbits=[dict(vertices=[0], original_leaf=0, word=[])])

    def test_required_edges_are_actual_cell_edges(self):
        # Vertex membership alone does not establish an edge: the second cell
        # has the same endpoints, but no edge between them.
        cells = [make_cell(0, 1, 3, [3], []), make_cell(1, 1, 3, [], []),
                 make_cell(2, 1, 5, [5], [])]
        formula = encode(cells, (0, 1), counter='totalizer', required_edges=3)
        clauses = [(rule['edge'], rule['owners'], clause)
                   for clause, rule in zip(formula.clauses, formula.rules) if rule['tag'] == 'edge']
        self.assertEqual(clauses, [(0, [0], [1]), (1, [2], [3])])
        empty = encode(cells, (0, 1), required_edges=1 << 44)
        self.assertEqual(empty.clauses[-1], [])
        with self.assertRaises(ValueError):
            encode(cells, (0, 1), required_edges=1 << 45)

    def test_terminal_orbit_words_go_from_the_orbit_to_the_leaf(self):
        # One 3-cycle needs words of length two. Reversing the generator order
        # or using forward maps to construct inverse images is observable here.
        width = 2
        forward, inverse = [1, 2, 0], [2, 0, 1]
        raw = dict(cellPred='2', framePred='0', leafPred='0', cellWidth=str(width),
                   cellMaps=str(pack(forward, width)),
                   inverseCellMaps=str(pack(inverse, width)),
                   leaves=f'⟨20, {2 | (pack([0, 1], width) << 16)}⟩')
        orbits = leaf_orbits(raw, [1, 1, 1], (0, 2))
        self.assertEqual({tuple(row['vertices']) for row in orbits}, {(0, 1), (0, 2), (1, 2)})
        self.assertEqual(sorted(len(row['word']) for row in orbits), [0, 1, 2])
        for row in orbits:
            vertices = row['vertices']
            for _ in row['word']:
                vertices = [forward[c] for c in vertices]
            self.assertEqual(sorted(vertices), [0, 1])
        bad = {**raw, 'inverseCellMaps': str(pack(forward, width))}
        with self.assertRaises(ValueError):
            leaf_orbits(bad, [1, 1, 1], (0, 2))

    def test_packed_cell_round_trip_matches_the_lean_layout(self):
        edges = [3, 5, 9, 6, 10, 12]
        ridges = [7, 11, 13, 14]
        cell = make_cell(0, 1, 15, edges, ridges)
        code = cell.cell_code
        self.assertEqual(code & 31, 1)
        self.assertEqual((code >> 5) & 1023, 15)
        count = (code >> 15) & 31
        self.assertEqual(count, len(edges))
        self.assertEqual([(code >> (20 + 10 * i)) & 1023 for i in range(count)], edges)
        offset = 20 + 10 * count
        count = (code >> offset) & 31
        self.assertEqual(count, len(ridges))
        self.assertEqual([(code >> (offset + 5 + 10 * i)) & 1023 for i in range(count)], ridges)


if __name__ == '__main__':
    unittest.main()
