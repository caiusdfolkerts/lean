"""Bound Linux VMA use without changing the Lean compiler or imported bytes.

Lean 4.35 uses file-backed MAP_FIXED_NOREPLACE mappings for olean regions.
A large import closure can exceed a container host's vm.max_map_count. Denying
only small mappings selects Lean's existing malloc/read/relocation fallback;
large regions stay mapped, avoiding unnecessary heap growth. The seccomp filter
only removes a syscall capability and is inherited by verification children.
"""
import ctypes
import hashlib
from pathlib import Path
import platform
import sys

SMALL_REGION_BYTES = 65536

def install_small_mmap_fallback():
    if sys.platform != 'linux' or platform.machine() != 'x86_64' or sys.byteorder != 'little':
        raise RuntimeError('The small-region mmap fallback requires little-endian Linux x86_64')
    class Filter(ctypes.Structure):
        _fields_ = [('code', ctypes.c_ushort), ('jt', ctypes.c_ubyte),
                    ('jf', ctypes.c_ubyte), ('k', ctypes.c_uint32)]
    class Program(ctypes.Structure):
        _fields_ = [('length', ctypes.c_ushort), ('instructions', ctypes.POINTER(Filter))]
    # struct seccomp_data: nr at 0, args at 16 (six uint64 values).
    # x86_64 mmap is syscall 9; args are addr, length, prot, flags, fd, offset.
    # Every branch other than a small file-backed MAP_FIXED_NOREPLACE is allowed.
    rows = [
        (0x20, 0, 0, 0),           # load syscall number
        (0x15, 0, 9, 9),           # other syscall -> allow
        (0x20, 0, 0, 48),          # load fd low word
        (0x15, 7, 0, 0xffffffff),  # anonymous fd -1 -> allow
        (0x20, 0, 0, 40),          # load flags low word
        (0x45, 0, 5, 0x100000),    # no MAP_FIXED_NOREPLACE -> allow
        (0x20, 0, 0, 28),          # load length high word
        (0x15, 0, 3, 0),           # length >= 2^32 -> allow
        (0x20, 0, 0, 24),          # load length low word
        (0x25, 1, 0, SMALL_REGION_BYTES),  # large region -> allow
        (0x06, 0, 0, 0x50000 | 12),       # SECCOMP_RET_ERRNO | ENOMEM
        (0x06, 0, 0, 0x7fff0000),         # SECCOMP_RET_ALLOW
    ]
    filters = (Filter * len(rows))(*(Filter(*row) for row in rows))
    program = Program(len(rows), filters)
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(38, 1, 0, 0, 0) != 0:  # PR_SET_NO_NEW_PRIVS
        raise OSError(ctypes.get_errno(), 'Could not set no_new_privs')
    if libc.prctl(22, 2, ctypes.byref(program), 0, 0) != 0:  # PR_SET_SECCOMP, FILTER
        raise OSError(ctypes.get_errno(), 'Could not install small-region mmap filter')
    return {'policy': 'small-file-mmap-fallback-v1', 'max_region_bytes': SMALL_REGION_BYTES,
            'host_max_map_count': int(Path('/proc/sys/vm/max_map_count').read_text()),
            'implementation_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
