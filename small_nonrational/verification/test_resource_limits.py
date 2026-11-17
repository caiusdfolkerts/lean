"""Exercise the actual Linux syscall filter in an isolated child process."""
import ctypes
import errno
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import unittest
from resource_limits import install_small_mmap_fallback

def probe():
    libc=ctypes.CDLL(None,use_errno=True)
    libc.mmap.restype=ctypes.c_void_p
    libc.mmap.argtypes=[ctypes.c_void_p,ctypes.c_size_t,ctypes.c_int,ctypes.c_int,ctypes.c_int,ctypes.c_long]
    libc.munmap.argtypes=[ctypes.c_void_p,ctypes.c_size_t]
    failed=ctypes.c_void_p(-1).value
    with tempfile.TemporaryFile() as source:
        source.write(b'checked bytes'+b'\0'*(131072-13));source.flush()
        # Obtain an unused address without relying on a platform-specific guess.
        address=libc.mmap(None,131072,3,0x22,-1,0)
        assert address != failed
        assert libc.munmap(address,131072)==0
        def mapping(length,flags,fd,denied=False):
            ctypes.set_errno(0)
            result=libc.mmap(address,length,3,flags,fd,0)
            if denied:
                assert result == failed and ctypes.get_errno()==errno.ENOMEM
            else:
                assert result != failed, ctypes.get_errno()
                if fd != -1:assert ctypes.string_at(result,13)==b'checked bytes'
                assert libc.munmap(result,length)==0
        mapping(65536,0x100002,source.fileno())
        policy=install_small_mmap_fallback()
        assert policy['max_region_bytes']==65536
        mapping(4096,0x100002,source.fileno(),denied=True)
        mapping(65536,0x100002,source.fileno(),denied=True)
        mapping(65537,0x100002,source.fileno())
        mapping(4096,0x100022,-1)
        mapping(4096,2,source.fileno())
        source.seek(0);assert source.read(13)==b'checked bytes'
    print('Small-region filter preserves large, anonymous and ordinary mappings and file bytes.')

class ResourceLimitTests(unittest.TestCase):
    @unittest.skipUnless(sys.platform=='linux' and platform.machine()=='x86_64','Linux x86_64 syscall test')
    def test_real_filter_in_child(self):
        subprocess.run([sys.executable,str(Path(__file__).resolve()),'--probe'],check=True,timeout=30)

if __name__=='__main__':
    if '--probe' in sys.argv:probe()
    else:unittest.main()
