module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 57344 57472 128
cert_checked_7 57472 57600 128
cert_checked_7 57600 57728 128
cert_checked_7 57728 57856 128
cert_checked_7 57856 57984 128
cert_checked_7 57984 58112 128
cert_checked_7 58112 58240 128
cert_checked_7 58240 58368 128
cert_checked_7 58368 58496 128
cert_checked_7 58496 58624 128
cert_checked_7 58624 58752 128
cert_checked_7 58752 58880 128
cert_checked_7 58880 59008 128
cert_checked_7 59008 59136 128
cert_checked_7 59136 59264 128
cert_checked_7 59264 59392 128
cert_checked_7 59392 59520 128
cert_checked_7 59520 59648 128
cert_checked_7 59648 59776 128
cert_checked_7 59776 59904 128
cert_checked_7 59904 60032 128
cert_checked_7 60032 60160 128
cert_checked_7 60160 60288 128
cert_checked_7 60288 60416 128
cert_checked_7 60416 60544 128
cert_checked_7 60544 60672 128
cert_checked_7 60672 60800 128
cert_checked_7 60800 60928 128
cert_checked_7 60928 60984 56
theorem interval_57344 : FiniteChecks.Interval test 57344 60984 :=
  (FiniteChecks.interval_append test 57344 59136 60984
  (FiniteChecks.interval_append test 57344 58240 59136
  (FiniteChecks.interval_append test 57344 57728 58240
  (FiniteChecks.interval_append test 57344 57472 57728
  checked_57344
  (FiniteChecks.interval_append test 57472 57600 57728
  checked_57472
  checked_57600))
  (FiniteChecks.interval_append test 57728 57984 58240
  (FiniteChecks.interval_append test 57728 57856 57984
  checked_57728
  checked_57856)
  (FiniteChecks.interval_append test 57984 58112 58240
  checked_57984
  checked_58112)))
  (FiniteChecks.interval_append test 58240 58624 59136
  (FiniteChecks.interval_append test 58240 58368 58624
  checked_58240
  (FiniteChecks.interval_append test 58368 58496 58624
  checked_58368
  checked_58496))
  (FiniteChecks.interval_append test 58624 58880 59136
  (FiniteChecks.interval_append test 58624 58752 58880
  checked_58624
  checked_58752)
  (FiniteChecks.interval_append test 58880 59008 59136
  checked_58880
  checked_59008))))
  (FiniteChecks.interval_append test 59136 60032 60984
  (FiniteChecks.interval_append test 59136 59520 60032
  (FiniteChecks.interval_append test 59136 59264 59520
  checked_59136
  (FiniteChecks.interval_append test 59264 59392 59520
  checked_59264
  checked_59392))
  (FiniteChecks.interval_append test 59520 59776 60032
  (FiniteChecks.interval_append test 59520 59648 59776
  checked_59520
  checked_59648)
  (FiniteChecks.interval_append test 59776 59904 60032
  checked_59776
  checked_59904)))
  (FiniteChecks.interval_append test 60032 60544 60984
  (FiniteChecks.interval_append test 60032 60288 60544
  (FiniteChecks.interval_append test 60032 60160 60288
  checked_60032
  checked_60160)
  (FiniteChecks.interval_append test 60288 60416 60544
  checked_60288
  checked_60416))
  (FiniteChecks.interval_append test 60544 60800 60984
  (FiniteChecks.interval_append test 60544 60672 60800
  checked_60544
  checked_60672)
  (FiniteChecks.interval_append test 60800 60928 60984
  checked_60800
  checked_60928)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
