"""Parallel auditing must preserve complete coverage and fail closed."""
import contextlib
import io
from pathlib import Path
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

import verify


class ParallelAuditTests(unittest.TestCase):
    def exercise(self, failed_batch=None):
        modules = [f'Module{i}' for i in range(200)]
        lock = threading.Lock()
        active = peak = 0
        seen = []

        def batch(roots, selected, lean, flags, env, directory, timeout):
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
