module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed009ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
open Papers.RationalityTen
cert_checked_4 00512 512 544 32
cert_checked_4 00544 544 576 32
cert_checked_4 00576 576 608 32
cert_checked_4 00608 608 640 32
cert_checked_4 00640 640 672 32
cert_checked_4 00672 672 704 32
cert_checked_4 00704 704 736 32
cert_checked_4 00736 736 768 32
cert_checked_4 00768 768 800 32
cert_checked_4 00800 800 832 32
cert_checked_4 00832 832 864 32
cert_checked_4 00864 864 896 32
cert_checked_4 00896 896 910 14
theorem part_001 : FiniteChecks.Interval test 512 910 :=
  (FiniteChecks.interval_append test 512 704 910
  (FiniteChecks.interval_append test 512 608 704
  (FiniteChecks.interval_append test 512 544 608
  checked_00512
  (FiniteChecks.interval_append test 544 576 608
  checked_00544
  checked_00576))
  (FiniteChecks.interval_append test 608 640 704
  checked_00608
  (FiniteChecks.interval_append test 640 672 704
  checked_00640
  checked_00672)))
  (FiniteChecks.interval_append test 704 800 910
  (FiniteChecks.interval_append test 704 736 800
  checked_00704
  (FiniteChecks.interval_append test 736 768 800
  checked_00736
  checked_00768))
  (FiniteChecks.interval_append test 800 864 910
  (FiniteChecks.interval_append test 800 832 864
  checked_00800
  checked_00832)
  (FiniteChecks.interval_append test 864 896 910
  checked_00864
  checked_00896))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
