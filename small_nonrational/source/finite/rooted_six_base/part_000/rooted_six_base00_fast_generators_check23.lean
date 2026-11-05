module
prelude
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_94208 : FiniteChecks.Interval test 94208 94336 :=
  FiniteChecks.interval_of_check test 94208 128 (by decide +kernel)
theorem checked_94336 : FiniteChecks.Interval test 94336 94464 :=
  FiniteChecks.interval_of_check test 94336 128 (by decide +kernel)
theorem checked_94464 : FiniteChecks.Interval test 94464 94592 :=
  FiniteChecks.interval_of_check test 94464 128 (by decide +kernel)
theorem checked_94592 : FiniteChecks.Interval test 94592 94720 :=
  FiniteChecks.interval_of_check test 94592 128 (by decide +kernel)
theorem checked_94720 : FiniteChecks.Interval test 94720 94848 :=
  FiniteChecks.interval_of_check test 94720 128 (by decide +kernel)
theorem checked_94848 : FiniteChecks.Interval test 94848 94976 :=
  FiniteChecks.interval_of_check test 94848 128 (by decide +kernel)
theorem checked_94976 : FiniteChecks.Interval test 94976 95104 :=
  FiniteChecks.interval_of_check test 94976 128 (by decide +kernel)
theorem checked_95104 : FiniteChecks.Interval test 95104 95232 :=
  FiniteChecks.interval_of_check test 95104 128 (by decide +kernel)
theorem checked_95232 : FiniteChecks.Interval test 95232 95360 :=
  FiniteChecks.interval_of_check test 95232 128 (by decide +kernel)
theorem checked_95360 : FiniteChecks.Interval test 95360 95488 :=
  FiniteChecks.interval_of_check test 95360 128 (by decide +kernel)
theorem checked_95488 : FiniteChecks.Interval test 95488 95616 :=
  FiniteChecks.interval_of_check test 95488 128 (by decide +kernel)
theorem checked_95616 : FiniteChecks.Interval test 95616 95744 :=
  FiniteChecks.interval_of_check test 95616 128 (by decide +kernel)
theorem checked_95744 : FiniteChecks.Interval test 95744 95872 :=
  FiniteChecks.interval_of_check test 95744 128 (by decide +kernel)
theorem checked_95872 : FiniteChecks.Interval test 95872 96000 :=
  FiniteChecks.interval_of_check test 95872 128 (by decide +kernel)
theorem checked_96000 : FiniteChecks.Interval test 96000 96128 :=
  FiniteChecks.interval_of_check test 96000 128 (by decide +kernel)
theorem checked_96128 : FiniteChecks.Interval test 96128 96256 :=
  FiniteChecks.interval_of_check test 96128 128 (by decide +kernel)
theorem checked_96256 : FiniteChecks.Interval test 96256 96384 :=
  FiniteChecks.interval_of_check test 96256 128 (by decide +kernel)
theorem checked_96384 : FiniteChecks.Interval test 96384 96512 :=
  FiniteChecks.interval_of_check test 96384 128 (by decide +kernel)
theorem checked_96512 : FiniteChecks.Interval test 96512 96640 :=
  FiniteChecks.interval_of_check test 96512 128 (by decide +kernel)
theorem checked_96640 : FiniteChecks.Interval test 96640 96768 :=
  FiniteChecks.interval_of_check test 96640 128 (by decide +kernel)
theorem checked_96768 : FiniteChecks.Interval test 96768 96896 :=
  FiniteChecks.interval_of_check test 96768 128 (by decide +kernel)
theorem checked_96896 : FiniteChecks.Interval test 96896 97024 :=
  FiniteChecks.interval_of_check test 96896 128 (by decide +kernel)
theorem checked_97024 : FiniteChecks.Interval test 97024 97152 :=
  FiniteChecks.interval_of_check test 97024 128 (by decide +kernel)
theorem checked_97152 : FiniteChecks.Interval test 97152 97280 :=
  FiniteChecks.interval_of_check test 97152 128 (by decide +kernel)
theorem checked_97280 : FiniteChecks.Interval test 97280 97408 :=
  FiniteChecks.interval_of_check test 97280 128 (by decide +kernel)
theorem checked_97408 : FiniteChecks.Interval test 97408 97536 :=
  FiniteChecks.interval_of_check test 97408 128 (by decide +kernel)
theorem checked_97536 : FiniteChecks.Interval test 97536 97664 :=
  FiniteChecks.interval_of_check test 97536 128 (by decide +kernel)
theorem checked_97664 : FiniteChecks.Interval test 97664 97792 :=
  FiniteChecks.interval_of_check test 97664 128 (by decide +kernel)
theorem checked_97792 : FiniteChecks.Interval test 97792 97920 :=
  FiniteChecks.interval_of_check test 97792 128 (by decide +kernel)
theorem checked_97920 : FiniteChecks.Interval test 97920 98048 :=
  FiniteChecks.interval_of_check test 97920 128 (by decide +kernel)
theorem checked_98048 : FiniteChecks.Interval test 98048 98176 :=
  FiniteChecks.interval_of_check test 98048 128 (by decide +kernel)
theorem checked_98176 : FiniteChecks.Interval test 98176 98304 :=
  FiniteChecks.interval_of_check test 98176 128 (by decide +kernel)
theorem interval_94208 : FiniteChecks.Interval test 94208 98304 :=
  (FiniteChecks.interval_append test 94208 96256 98304
  (FiniteChecks.interval_append test 94208 95232 96256
  (FiniteChecks.interval_append test 94208 94720 95232
  (FiniteChecks.interval_append test 94208 94464 94720
  (FiniteChecks.interval_append test 94208 94336 94464
  checked_94208
  checked_94336)
  (FiniteChecks.interval_append test 94464 94592 94720
  checked_94464
  checked_94592))
  (FiniteChecks.interval_append test 94720 94976 95232
  (FiniteChecks.interval_append test 94720 94848 94976
  checked_94720
  checked_94848)
  (FiniteChecks.interval_append test 94976 95104 95232
  checked_94976
  checked_95104)))
  (FiniteChecks.interval_append test 95232 95744 96256
  (FiniteChecks.interval_append test 95232 95488 95744
  (FiniteChecks.interval_append test 95232 95360 95488
  checked_95232
  checked_95360)
  (FiniteChecks.interval_append test 95488 95616 95744
  checked_95488
  checked_95616))
  (FiniteChecks.interval_append test 95744 96000 96256
  (FiniteChecks.interval_append test 95744 95872 96000
  checked_95744
  checked_95872)
  (FiniteChecks.interval_append test 96000 96128 96256
  checked_96000
  checked_96128))))
  (FiniteChecks.interval_append test 96256 97280 98304
  (FiniteChecks.interval_append test 96256 96768 97280
  (FiniteChecks.interval_append test 96256 96512 96768
  (FiniteChecks.interval_append test 96256 96384 96512
  checked_96256
  checked_96384)
  (FiniteChecks.interval_append test 96512 96640 96768
  checked_96512
  checked_96640))
  (FiniteChecks.interval_append test 96768 97024 97280
  (FiniteChecks.interval_append test 96768 96896 97024
  checked_96768
  checked_96896)
  (FiniteChecks.interval_append test 97024 97152 97280
  checked_97024
  checked_97152)))
  (FiniteChecks.interval_append test 97280 97792 98304
  (FiniteChecks.interval_append test 97280 97536 97792
  (FiniteChecks.interval_append test 97280 97408 97536
  checked_97280
  checked_97408)
  (FiniteChecks.interval_append test 97536 97664 97792
  checked_97536
  checked_97664))
  (FiniteChecks.interval_append test 97792 98048 98304
  (FiniteChecks.interval_append test 97792 97920 98048
  checked_97792
  checked_97920)
  (FiniteChecks.interval_append test 98048 98176 98304
  checked_98048
  checked_98176)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
