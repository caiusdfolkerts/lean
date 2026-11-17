"""Exercise resource admission and failure propagation with a fake compiler."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

COMPILER = Path(__file__).with_name('compile.py')
HEAVY = 'ToricPower.ReconstructionCompletionRawSquare'


class ResourceTests(unittest.TestCase):
    def run_fixture(self, mode='pass', budget=10000):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / '.lake/packages').mkdir(parents=True)
            (root / 'ToricPower').mkdir()
            (root / 'Audit.lean').write_text(f'import LightA\nimport LightB\nimport {HEAVY}\n')
            for name in ('LightA', 'LightB', HEAVY):
                (root / (name.replace('.', '/') + '.lean')).write_text('-- fixture\n')
            binary = root / 'lean'
            binary.write_text(f'#!{sys.executable}\n' + '''
import json, os, pathlib, sys, time
if '--version' in sys.argv:
    print('Lean (version 4.35.0)')
    sys.exit(0)
source = next(x for x in sys.argv if x.endswith('.lean'))
memory = int(next(x[2:] for x in sys.argv if x.startswith('-M')))
def event(kind):
    with open('events.jsonl', 'a') as log:
        log.write(json.dumps({'kind':kind, 'source':source, 'memory':memory, 'time':time.monotonic()}) + '\\n')
event('start')
time.sleep(0.15)
mode = os.environ['FIXTURE_MODE']
if source.endswith('LightA.lean') and mode in ('memory', 'memory_always', 'ordinary_error'):
    if memory < 10000 or mode != 'memory':
        print('(kernel) excessive memory consumption detected' if mode != 'ordinary_error' else 'type mismatch')
        event('end')
        sys.exit(1)
if source.endswith('RawSquare.lean'):
    if memory < 10000 or mode == 'fail':
        event('end')
        sys.exit(1)
    if mode == 'sorry':
        print("declaration uses 'sorry'")
pathlib.Path(sys.argv[sys.argv.index('-o') + 1]).write_text('fixture output')
event('end')
''')
            binary.chmod(0o755)
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ['PATH'], FIXTURE_MODE=mode)
            result = subprocess.run(
                [sys.executable, str(COMPILER), str(root), '--workers', '4',
                 '--memory-budget-mb', str(budget)], env=env, capture_output=True, text=True)
            events_path = root / 'events.jsonl'
            events = [json.loads(line) for line in events_path.read_text().splitlines()] if events_path.exists() else []
            records_path = root / 'verification/kernel/results.json'
            records = json.loads(records_path.read_text()) if records_path.exists() else {}
            return result, events, records

    def test_memory_budget_and_dependency_order(self):
        result, events, records = self.run_fixture()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        active = {}
        peak_jobs = 0
        for event in sorted(events, key=lambda e: e['time']):
            if event['kind'] == 'start':
                active[event['source']] = event['memory']
                peak_jobs = max(peak_jobs, len(active))
                self.assertLessEqual(sum(active.values()), 10000)
                if event['source'].endswith('Audit.lean'):
                    self.assertEqual(len(active), 1)
            else:
                active.pop(event['source'])
        self.assertEqual(peak_jobs, 2)
        self.assertTrue(all(r['status'] == 'passed' for r in records.values()))

    def test_failure_blocks_audit(self):
        for mode in ('fail', 'sorry'):
            with self.subTest(mode=mode):
                result, _, records = self.run_fixture(mode)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(records[HEAVY]['status'], 'failed')
                self.assertEqual(records['Audit']['status'], 'blocked')

    def test_memory_retry_is_bounded_and_serial(self):
        for mode in ('memory', 'memory_always', 'ordinary_error'):
            with self.subTest(mode=mode):
                result, events, records = self.run_fixture(mode)
                attempts = [e['memory'] for e in events if e['kind'] == 'start' and e['source'].endswith('LightA.lean')]
                self.assertEqual(attempts, [5000] if mode == 'ordinary_error' else [5000, 10000])
                self.assertEqual(result.returncode == 0, mode == 'memory')
                self.assertEqual(records['Audit']['status'], 'passed' if mode == 'memory' else 'blocked')
                active = {}
                for event in sorted(events, key=lambda e: e['time']):
                    if event['kind'] == 'start':
                        active[event['source']] = event['memory']
                        self.assertLessEqual(sum(active.values()), 10000)
                    else:
                        active.pop(event['source'])

    def test_impossible_budget_rejected(self):
        result, events, _ = self.run_fixture(budget=9999)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('too small', result.stderr)
        self.assertEqual(events, [])


if __name__ == '__main__':
    unittest.main()
