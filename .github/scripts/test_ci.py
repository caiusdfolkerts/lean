"""Regression checks for project isolation and honest aggregate status."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from aggregate_status import fingerprint, latest_main_run, verdict


class StatusTests(unittest.TestCase):
    def test_only_latest_main_build_counts(self):
        def run(number, branch='main', event='push'):
            return {'id': number, 'head_branch': branch, 'event': event}
        runs = [run(1), run(2), run(3, 'feature'), run(4, event='pull_request')]
        self.assertEqual(latest_main_run(runs)['id'], 2)
        self.assertIsNone(latest_main_run([run(3, 'feature')]))

    def test_fail_closed(self):
        success = {'status': 'completed', 'conclusion': 'success'}
        self.assertEqual(verdict(success, 'same', 'same'), 'Passed')
        self.assertNotEqual(verdict(success, 'new', 'old'), 'Passed')
        self.assertNotEqual(verdict(None, 'new', None), 'Passed')
        for status, conclusion in [('queued', None), ('in_progress', None),
                                   ('completed', 'failure'), ('completed', 'cancelled'),
                                   ('completed', 'skipped'), ('completed', 'timed_out')]:
            self.assertNotEqual(verdict({'status': status, 'conclusion': conclusion}, 'x', 'x'), 'Passed')


class InputTests(unittest.TestCase):
    def test_docs_other_projects_and_build_inputs(self):
        original = Path.cwd()
        with tempfile.TemporaryDirectory() as temp:
            try:
                os.chdir(temp)
                subprocess.run(['git', 'init', '-q'], check=True)
                def commit(path, content):
                    file = Path(path)
                    file.parent.mkdir(parents=True, exist_ok=True)
                    file.write_text(content)
                    subprocess.run(['git', 'add', '.'], check=True)
                    subprocess.run(['git', '-c', 'user.name=Test', '-c', 'user.email=test@example.com',
                                    'commit', '-qm', 'fixture'], check=True)
                commit('alpha/Main.lean', 'theorem fixture : True := trivial')
                baseline = fingerprint('HEAD', 'alpha')
                for path in ['README.md', 'alpha/README.md', 'alpha/docs/notes.md',
                             'alpha/paper.pdf', 'beta/Main.lean']:
                    commit(path, 'documentation or another project')
                    self.assertEqual(fingerprint('HEAD', 'alpha'), baseline, path)
                for path in ['alpha/Main.lean', 'alpha/lean-toolchain', 'alpha/lake-manifest.json',
                             'alpha/verification/run.py', 'alpha/verification/source_index.json',
                             '.github/workflows/project-alpha.yml', '.github/workflows/build-project.yml']:
                    commit(path, 'changed build input')
                    updated = fingerprint('HEAD', 'alpha')
                    self.assertNotEqual(updated, baseline, path)
                    baseline = updated
                Path('alpha/Main.lean').unlink()
                commit('alpha/another.lean', 'renamed source')
                self.assertNotEqual(fingerprint('HEAD', 'alpha'), baseline)
            finally:
                os.chdir(original)


if __name__ == '__main__':
    unittest.main()
