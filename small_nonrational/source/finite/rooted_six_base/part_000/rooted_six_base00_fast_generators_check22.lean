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
theorem checked_90112 : FiniteChecks.Interval test 90112 90240 :=
  FiniteChecks.interval_of_check test 90112 128 (by decide +kernel)
theorem checked_90240 : FiniteChecks.Interval test 90240 90368 :=
  FiniteChecks.interval_of_check test 90240 128 (by decide +kernel)
theorem checked_90368 : FiniteChecks.Interval test 90368 90496 :=
  FiniteChecks.interval_of_check test 90368 128 (by decide +kernel)
theorem checked_90496 : FiniteChecks.Interval test 90496 90624 :=
  FiniteChecks.interval_of_check test 90496 128 (by decide +kernel)
theorem checked_90624 : FiniteChecks.Interval test 90624 90752 :=
  FiniteChecks.interval_of_check test 90624 128 (by decide +kernel)
theorem checked_90752 : FiniteChecks.Interval test 90752 90880 :=
  FiniteChecks.interval_of_check test 90752 128 (by decide +kernel)
theorem checked_90880 : FiniteChecks.Interval test 90880 91008 :=
  FiniteChecks.interval_of_check test 90880 128 (by decide +kernel)
theorem checked_91008 : FiniteChecks.Interval test 91008 91136 :=
  FiniteChecks.interval_of_check test 91008 128 (by decide +kernel)
theorem checked_91136 : FiniteChecks.Interval test 91136 91264 :=
  FiniteChecks.interval_of_check test 91136 128 (by decide +kernel)
theorem checked_91264 : FiniteChecks.Interval test 91264 91392 :=
  FiniteChecks.interval_of_check test 91264 128 (by decide +kernel)
theorem checked_91392 : FiniteChecks.Interval test 91392 91520 :=
  FiniteChecks.interval_of_check test 91392 128 (by decide +kernel)
theorem checked_91520 : FiniteChecks.Interval test 91520 91648 :=
  FiniteChecks.interval_of_check test 91520 128 (by decide +kernel)
theorem checked_91648 : FiniteChecks.Interval test 91648 91776 :=
  FiniteChecks.interval_of_check test 91648 128 (by decide +kernel)
theorem checked_91776 : FiniteChecks.Interval test 91776 91904 :=
  FiniteChecks.interval_of_check test 91776 128 (by decide +kernel)
theorem checked_91904 : FiniteChecks.Interval test 91904 92032 :=
  FiniteChecks.interval_of_check test 91904 128 (by decide +kernel)
theorem checked_92032 : FiniteChecks.Interval test 92032 92160 :=
  FiniteChecks.interval_of_check test 92032 128 (by decide +kernel)
theorem checked_92160 : FiniteChecks.Interval test 92160 92288 :=
  FiniteChecks.interval_of_check test 92160 128 (by decide +kernel)
theorem checked_92288 : FiniteChecks.Interval test 92288 92416 :=
  FiniteChecks.interval_of_check test 92288 128 (by decide +kernel)
theorem checked_92416 : FiniteChecks.Interval test 92416 92544 :=
  FiniteChecks.interval_of_check test 92416 128 (by decide +kernel)
theorem checked_92544 : FiniteChecks.Interval test 92544 92672 :=
  FiniteChecks.interval_of_check test 92544 128 (by decide +kernel)
theorem checked_92672 : FiniteChecks.Interval test 92672 92800 :=
  FiniteChecks.interval_of_check test 92672 128 (by decide +kernel)
theorem checked_92800 : FiniteChecks.Interval test 92800 92928 :=
  FiniteChecks.interval_of_check test 92800 128 (by decide +kernel)
theorem checked_92928 : FiniteChecks.Interval test 92928 93056 :=
  FiniteChecks.interval_of_check test 92928 128 (by decide +kernel)
theorem checked_93056 : FiniteChecks.Interval test 93056 93184 :=
  FiniteChecks.interval_of_check test 93056 128 (by decide +kernel)
theorem checked_93184 : FiniteChecks.Interval test 93184 93312 :=
  FiniteChecks.interval_of_check test 93184 128 (by decide +kernel)
theorem checked_93312 : FiniteChecks.Interval test 93312 93440 :=
  FiniteChecks.interval_of_check test 93312 128 (by decide +kernel)
theorem checked_93440 : FiniteChecks.Interval test 93440 93568 :=
  FiniteChecks.interval_of_check test 93440 128 (by decide +kernel)
theorem checked_93568 : FiniteChecks.Interval test 93568 93696 :=
  FiniteChecks.interval_of_check test 93568 128 (by decide +kernel)
theorem checked_93696 : FiniteChecks.Interval test 93696 93824 :=
  FiniteChecks.interval_of_check test 93696 128 (by decide +kernel)
theorem checked_93824 : FiniteChecks.Interval test 93824 93952 :=
  FiniteChecks.interval_of_check test 93824 128 (by decide +kernel)
theorem checked_93952 : FiniteChecks.Interval test 93952 94080 :=
  FiniteChecks.interval_of_check test 93952 128 (by decide +kernel)
theorem checked_94080 : FiniteChecks.Interval test 94080 94208 :=
  FiniteChecks.interval_of_check test 94080 128 (by decide +kernel)
theorem interval_90112 : FiniteChecks.Interval test 90112 94208 :=
  (FiniteChecks.interval_append test 90112 92160 94208
  (FiniteChecks.interval_append test 90112 91136 92160
  (FiniteChecks.interval_append test 90112 90624 91136
  (FiniteChecks.interval_append test 90112 90368 90624
  (FiniteChecks.interval_append test 90112 90240 90368
  checked_90112
  checked_90240)
  (FiniteChecks.interval_append test 90368 90496 90624
  checked_90368
  checked_90496))
  (FiniteChecks.interval_append test 90624 90880 91136
  (FiniteChecks.interval_append test 90624 90752 90880
  checked_90624
  checked_90752)
  (FiniteChecks.interval_append test 90880 91008 91136
  checked_90880
  checked_91008)))
  (FiniteChecks.interval_append test 91136 91648 92160
  (FiniteChecks.interval_append test 91136 91392 91648
  (FiniteChecks.interval_append test 91136 91264 91392
  checked_91136
  checked_91264)
  (FiniteChecks.interval_append test 91392 91520 91648
  checked_91392
  checked_91520))
  (FiniteChecks.interval_append test 91648 91904 92160
  (FiniteChecks.interval_append test 91648 91776 91904
  checked_91648
  checked_91776)
  (FiniteChecks.interval_append test 91904 92032 92160
  checked_91904
  checked_92032))))
  (FiniteChecks.interval_append test 92160 93184 94208
  (FiniteChecks.interval_append test 92160 92672 93184
  (FiniteChecks.interval_append test 92160 92416 92672
  (FiniteChecks.interval_append test 92160 92288 92416
  checked_92160
  checked_92288)
  (FiniteChecks.interval_append test 92416 92544 92672
  checked_92416
  checked_92544))
  (FiniteChecks.interval_append test 92672 92928 93184
  (FiniteChecks.interval_append test 92672 92800 92928
  checked_92672
  checked_92800)
  (FiniteChecks.interval_append test 92928 93056 93184
  checked_92928
  checked_93056)))
  (FiniteChecks.interval_append test 93184 93696 94208
  (FiniteChecks.interval_append test 93184 93440 93696
  (FiniteChecks.interval_append test 93184 93312 93440
  checked_93184
  checked_93312)
  (FiniteChecks.interval_append test 93440 93568 93696
  checked_93440
  checked_93568))
  (FiniteChecks.interval_append test 93696 93952 94208
  (FiniteChecks.interval_append test 93696 93824 93952
  checked_93696
  checked_93824)
  (FiniteChecks.interval_append test 93952 94080 94208
  checked_93952
  checked_94080)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
