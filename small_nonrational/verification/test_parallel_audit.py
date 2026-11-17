"""Parallel auditing must preserve complete coverage and fail closed."""
import contextlib
import io
from pathlib import Path
import tempfile
import threading
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import verify


class ParallelAuditTests(unittest.TestCase):
    def test_memory_retries_release_and_reserve_full_caps(self):
        budget = verify.LeanMemoryBudget(8, retry_memory=8)
        lock = threading.Lock()
        active = peak = 0
        def run(command, **kwargs):
            nonlocal active, peak
            cap = int(next(x[2:] for x in command if x.startswith('-M')))
            with lock:
                active += cap
                peak = max(peak, active)
            time.sleep(0.01)
            if cap == 2:
                kwargs['stdout'].write('(kernel) excessive memory consumption detected\n')
            with lock:
                active -= cap
            return SimpleNamespace(returncode=1 if cap == 2 else 0)
        with tempfile.TemporaryDirectory() as temp, patch.object(verify.subprocess, 'run', run), contextlib.redirect_stdout(io.StringIO()):
            def check(index):
                return budget.run(['lean', '-M2'], {}, Path(temp)/f'{index}.log', 10)
            results = list(verify.bounded_parallel_map(check, range(8), 4))
            self.assertTrue(all(command == ['lean', '-M8'] and code == 0 for command, code in results))
            self.assertEqual(len(list(Path(temp).glob('*.memory-2.log'))), 8)
        self.assertLessEqual(peak, 8)
        self.assertEqual(budget.available, 8)

    def test_non_memory_errors_are_not_retried(self):
        budget = verify.LeanMemoryBudget(8, retry_memory=8)
        def fail(command, **kwargs):
            kwargs['stdout'].write('Unapproved axiom\n')
            return SimpleNamespace(returncode=1)
        with tempfile.TemporaryDirectory() as temp, patch.object(verify.subprocess, 'run', side_effect=fail) as run:
            command, code = budget.run(['lean', '-M2'], {}, Path(temp)/'error.log', 10)
            self.assertEqual((command, code), (['lean', '-M2'], 1))
            self.assertEqual(run.call_count, 1)
        self.assertEqual(budget.available, 8)

    def test_retry_limit_and_timeout_fail_closed(self):
        budget = verify.LeanMemoryBudget(8, retry_memory=8)
        def fail(command, **kwargs):
            kwargs['stdout'].write('excessive memory consumption detected\n')
            return SimpleNamespace(returncode=1)
        with tempfile.TemporaryDirectory() as temp, patch.object(verify.subprocess, 'run', side_effect=fail) as run, contextlib.redirect_stdout(io.StringIO()):
            command, code = budget.run(['lean', '-M2'], {}, Path(temp)/'limit.log', 10)
            self.assertEqual((command, code), (['lean', '-M8'], 1))
            self.assertEqual(run.call_count, 2)
        with tempfile.TemporaryDirectory() as temp, patch.object(verify.subprocess, 'run', side_effect=verify.subprocess.TimeoutExpired(['lean'], 10)) as run:
            _, code = budget.run(['lean', '-M2'], {}, Path(temp)/'timeout.log', 10)
            self.assertEqual(code, 124)
            self.assertEqual(run.call_count, 1)
        self.assertEqual(budget.available, 8)

    def test_bounded_map_order_and_failure(self):
        lock = threading.Lock()
        active = peak = 0
        def work(number):
            nonlocal active, peak
            with lock:
                active += 1
                peak = max(peak, active)
            time.sleep(0.04 if number == 0 else 0.01)
            with lock:
                active -= 1
            return number
        self.assertEqual(list(verify.bounded_parallel_map(work, range(9), 3)), list(range(9)))
        self.assertEqual(peak, 3)
        def fail(number):
            if number == 2:
                raise RuntimeError('failed batch')
            return number
        with self.assertRaisesRegex(RuntimeError, 'failed batch'):
            list(verify.bounded_parallel_map(fail, range(9), 3))
        self.assertEqual(list(verify.bounded_parallel_map(work, [], 3)), [])

    def test_bounded_map_does_not_exhaust_input(self):
        consumed = []
        def items():
            for number in range(100):
                consumed.append(number)
                yield number
        output = verify.bounded_parallel_map(lambda x: x, items(), 3)
        self.assertEqual(next(output), 0)
        self.assertEqual(len(consumed), 13)
        output.close()

    def exercise(self, failed_batch=None):
        modules = [f'Module{i}' for i in range(200)]
        lock = threading.Lock()
        active = peak = 0
        seen = []

        def batch(roots, selected, lean, flags, env, directory, timeout, memory_budget=None):
            nonlocal active, peak
            self.assertEqual(roots, selected)
            number = int(directory.name)
            with lock:
                active += 1
                peak = max(peak, active)
                seen.extend(selected)
            # Finish out of order to exercise deterministic report assembly.
            time.sleep(0.04 if number == 0 else 0.01)
            with lock:
                active -= 1
            return {'passed': number != failed_batch, 'modules': selected, 'declarations': len(selected)}

        with tempfile.TemporaryDirectory() as temp, patch.object(verify, 'closure_axiom_batch', batch), contextlib.redirect_stdout(io.StringIO()):
            report = verify.closure_axiom_audit(['Module199'], modules, 'lean', [], {}, Path(temp), 60, jobs=3)
        self.assertEqual(peak, 3)
        self.assertCountEqual(seen, modules)
        self.assertEqual(report['covered_modules'], modules)
        self.assertEqual(report['declarations'], len(modules))
        return report

    def test_all_batches_required(self):
        self.assertTrue(self.exercise()['passed'])

    def test_failed_batch_fails_entire_audit(self):
        self.assertFalse(self.exercise(failed_batch=1)['passed'])


if __name__ == '__main__':
    unittest.main()
