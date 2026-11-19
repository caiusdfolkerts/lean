"""Native proof producers never admit arbitrary plugins or inherited tool flags."""
from copy import deepcopy
from pathlib import Path
import os
import sys
import tempfile
import time
import unittest

import verify


class NativeProducerTests(unittest.TestCase):
    def plugin(self, name='RupProofTerm'):
        return {'module': name,
                'path': f'.lake/build/verification/native/{name}/lib{name}.so',
                'initializer': verify.NATIVE_PRODUCERS[name], 'sha256': 'a' * 64}

    def test_exact_plugin_allowlist(self):
        plugin = self.plugin()
        self.assertEqual(verify.native_plugin_flags([plugin], Path('/fixture')),
            ['--plugin=/fixture/.lake/build/verification/native/RupProofTerm/'
             'libRupProofTerm.so=initialize_RupProofTerm'])
        for key, value in [('module', 'ForeignPlugin'), ('initializer', 'initialize_Other'),
                           ('path', '/tmp/other.so'), ('sha256', 'not-a-hash')]:
            invalid = dict(plugin, **{key: value})
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                verify.native_plugin_flags([invalid], '/fixture')
        for plugins in [[plugin, plugin], [plugin, self.plugin('FacetSatInitials')]]:
            with self.assertRaises(RuntimeError):
                verify.native_plugin_flags(plugins, '/fixture')

    def test_compiler_environment_is_not_inherited(self):
        env = {key: 'untrusted' for key in ['LEAN_CC', 'LEAN_SYSROOT', 'CFLAGS', 'CPATH',
               'CLANG_CONFIG_FILE_USER_DIR', 'LD_PRELOAD', 'DYLD_INSERT_LIBRARIES']}
        env['PATH'] = '/pinned/bin:/usr/bin'
        self.assertEqual(verify.native_compile_environment(env), {'PATH': env['PATH']})

    def test_plain_source_fingerprints_remain_compatible(self):
        expected = verify.digest_json({'format': verify.FORMAT, 'source': 'source',
            'external_environment': 'environment', 'flags': ['-t1'], 'dependencies': {}})
        self.assertEqual(verify.source_fingerprint('source', 'environment', ['-t1'], {}), expected)
        self.assertNotEqual(verify.source_fingerprint('source', 'environment', ['-t1'], {},
                                                      [self.plugin()]), expected)

    def test_bundled_toolchain_inventory_binds_library_aliases(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp).resolve() / 'toolchain'
            for directory in ['bin', 'include', 'lib']:
                (prefix / directory).mkdir(parents=True)
            for name in ['leanc', 'clang', 'ld.lld']:
                (prefix / 'bin' / name).write_text(name)
            (prefix / 'include/runtime.h').write_text('header')
            (prefix / 'lib/first.so').write_text('first library')
            (prefix / 'lib/second.so').write_text('second library')
            alias = prefix / 'lib/selected.so'
            alias.symlink_to('first.so')
            before = verify.native_toolchain_inventory(prefix)
            verify.check_native_toolchain(prefix, before)
            alias.unlink()
            alias.symlink_to('second.so')
            after = verify.native_toolchain_inventory(prefix)
            self.assertNotEqual(before[str(alias)], after[str(alias)])
            with self.assertRaisesRegex(RuntimeError, 'toolchain inventory changed'):
                verify.check_native_toolchain(prefix, before)
            outside = Path(tmp) / 'external-clang'
            outside.write_text('not bundled')
            clang = prefix / 'bin/clang'
            clang.unlink()
            clang.symlink_to(outside)
            with self.assertRaisesRegex(RuntimeError, 'escapes its pinned prefix'):
                verify.native_toolchain_inventory(prefix)

    def test_native_timeout_stops_driver_children(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            marker = root / 'child-survived'
            child = 'import pathlib,time; time.sleep(0.5); pathlib.Path(' + repr(str(marker)) + ').touch()'
            driver = 'import subprocess,sys,time; subprocess.Popen([sys.executable,"-c",' + repr(child) + ']); time.sleep(30)'
            code = verify.run_native_command([sys.executable, '-c', driver], root, os.environ.copy(),
                                             root / 'driver.log', 0.1)
            self.assertEqual(code, 124)
            time.sleep(0.6)
            self.assertFalse(marker.exists())

    def test_native_artifacts_and_commands_are_all_authenticated(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            name = 'RupProofTerm'
            spec = verify.native_producer_spec(name, root / 'toolchain', {'compiler': 'hash'})
            stage = root / '.lake/build/verification/staging/fixture'
            directory = root / '.lake/build/verification/native' / name
            stage.mkdir(parents=True)
            directory.mkdir(parents=True)
            source = stage / (name + '.c')
            commands = verify.native_commands(spec, source)
            artifacts = []
            for filename in [name + '.c', name + '.o', 'lib' + name + '.so', 'compile.log', 'link.log']:
                path = directory / filename
                path.write_text(filename)
                artifacts.append({'path': str(path.relative_to(root)), 'sha256': verify.hash_file(path)})
            record = {'module': name, 'source_sha256': 'source',
                'command': ['lean', '-R', str(root / 'Sources'), '-o', str(stage / (name + '.olean')),
                            '-c', str(source), str(root / 'Sources' / (name + '.lean'))],
                'native_producer': {**spec, 'source_sha256': 'source', 'passed': True,
                    'compile_exit_code': 0, 'link_exit_code': 0, 'compile_command': commands[0],
                    'link_command': commands[1], 'artifacts': artifacts}}
            self.assertEqual(len(verify.native_artifact_values(record, root, spec)), 5)
            with self.assertRaisesRegex(RuntimeError, 'Unexpected native producer receipt'):
                verify.native_artifact_values(record, root, None)
            altered = deepcopy(record)
            altered['native_producer']['link_command'].append('/tmp/untracked.so')
            with self.assertRaisesRegex(RuntimeError, 'Unrecognized native build commands'):
                verify.native_artifact_values(altered, root, spec)
            extra = directory / 'untracked.so'
            extra.write_text('unexpected')
            with self.assertRaisesRegex(RuntimeError, 'Unexpected native producer directory'):
                verify.native_artifact_values(record, root, spec)
            extra.unlink()
            (directory / (name + '.o')).write_text('changed object')
            with self.assertRaisesRegex(RuntimeError, 'Changed native producer artifact'):
                verify.native_artifact_values(record, root, spec)


if __name__ == '__main__':
    unittest.main()
