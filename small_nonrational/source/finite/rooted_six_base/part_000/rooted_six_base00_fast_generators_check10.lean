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
theorem checked_40960 : FiniteChecks.Interval test 40960 41088 :=
  FiniteChecks.interval_of_check test 40960 128 (by decide +kernel)
theorem checked_41088 : FiniteChecks.Interval test 41088 41216 :=
  FiniteChecks.interval_of_check test 41088 128 (by decide +kernel)
theorem checked_41216 : FiniteChecks.Interval test 41216 41344 :=
  FiniteChecks.interval_of_check test 41216 128 (by decide +kernel)
theorem checked_41344 : FiniteChecks.Interval test 41344 41472 :=
  FiniteChecks.interval_of_check test 41344 128 (by decide +kernel)
theorem checked_41472 : FiniteChecks.Interval test 41472 41600 :=
  FiniteChecks.interval_of_check test 41472 128 (by decide +kernel)
theorem checked_41600 : FiniteChecks.Interval test 41600 41728 :=
  FiniteChecks.interval_of_check test 41600 128 (by decide +kernel)
theorem checked_41728 : FiniteChecks.Interval test 41728 41856 :=
  FiniteChecks.interval_of_check test 41728 128 (by decide +kernel)
theorem checked_41856 : FiniteChecks.Interval test 41856 41984 :=
  FiniteChecks.interval_of_check test 41856 128 (by decide +kernel)
theorem checked_41984 : FiniteChecks.Interval test 41984 42112 :=
  FiniteChecks.interval_of_check test 41984 128 (by decide +kernel)
theorem checked_42112 : FiniteChecks.Interval test 42112 42240 :=
  FiniteChecks.interval_of_check test 42112 128 (by decide +kernel)
theorem checked_42240 : FiniteChecks.Interval test 42240 42368 :=
  FiniteChecks.interval_of_check test 42240 128 (by decide +kernel)
theorem checked_42368 : FiniteChecks.Interval test 42368 42496 :=
  FiniteChecks.interval_of_check test 42368 128 (by decide +kernel)
theorem checked_42496 : FiniteChecks.Interval test 42496 42624 :=
  FiniteChecks.interval_of_check test 42496 128 (by decide +kernel)
theorem checked_42624 : FiniteChecks.Interval test 42624 42752 :=
  FiniteChecks.interval_of_check test 42624 128 (by decide +kernel)
theorem checked_42752 : FiniteChecks.Interval test 42752 42880 :=
  FiniteChecks.interval_of_check test 42752 128 (by decide +kernel)
theorem checked_42880 : FiniteChecks.Interval test 42880 43008 :=
  FiniteChecks.interval_of_check test 42880 128 (by decide +kernel)
theorem checked_43008 : FiniteChecks.Interval test 43008 43136 :=
  FiniteChecks.interval_of_check test 43008 128 (by decide +kernel)
theorem checked_43136 : FiniteChecks.Interval test 43136 43264 :=
  FiniteChecks.interval_of_check test 43136 128 (by decide +kernel)
theorem checked_43264 : FiniteChecks.Interval test 43264 43392 :=
  FiniteChecks.interval_of_check test 43264 128 (by decide +kernel)
theorem checked_43392 : FiniteChecks.Interval test 43392 43520 :=
  FiniteChecks.interval_of_check test 43392 128 (by decide +kernel)
theorem checked_43520 : FiniteChecks.Interval test 43520 43648 :=
  FiniteChecks.interval_of_check test 43520 128 (by decide +kernel)
theorem checked_43648 : FiniteChecks.Interval test 43648 43776 :=
  FiniteChecks.interval_of_check test 43648 128 (by decide +kernel)
theorem checked_43776 : FiniteChecks.Interval test 43776 43904 :=
  FiniteChecks.interval_of_check test 43776 128 (by decide +kernel)
theorem checked_43904 : FiniteChecks.Interval test 43904 44032 :=
  FiniteChecks.interval_of_check test 43904 128 (by decide +kernel)
theorem checked_44032 : FiniteChecks.Interval test 44032 44160 :=
  FiniteChecks.interval_of_check test 44032 128 (by decide +kernel)
theorem checked_44160 : FiniteChecks.Interval test 44160 44288 :=
  FiniteChecks.interval_of_check test 44160 128 (by decide +kernel)
theorem checked_44288 : FiniteChecks.Interval test 44288 44416 :=
  FiniteChecks.interval_of_check test 44288 128 (by decide +kernel)
theorem checked_44416 : FiniteChecks.Interval test 44416 44544 :=
  FiniteChecks.interval_of_check test 44416 128 (by decide +kernel)
theorem checked_44544 : FiniteChecks.Interval test 44544 44672 :=
  FiniteChecks.interval_of_check test 44544 128 (by decide +kernel)
theorem checked_44672 : FiniteChecks.Interval test 44672 44800 :=
  FiniteChecks.interval_of_check test 44672 128 (by decide +kernel)
theorem checked_44800 : FiniteChecks.Interval test 44800 44928 :=
  FiniteChecks.interval_of_check test 44800 128 (by decide +kernel)
theorem checked_44928 : FiniteChecks.Interval test 44928 45056 :=
  FiniteChecks.interval_of_check test 44928 128 (by decide +kernel)
theorem interval_40960 : FiniteChecks.Interval test 40960 45056 :=
  (FiniteChecks.interval_append test 40960 43008 45056
  (FiniteChecks.interval_append test 40960 41984 43008
  (FiniteChecks.interval_append test 40960 41472 41984
  (FiniteChecks.interval_append test 40960 41216 41472
  (FiniteChecks.interval_append test 40960 41088 41216
  checked_40960
  checked_41088)
  (FiniteChecks.interval_append test 41216 41344 41472
  checked_41216
  checked_41344))
  (FiniteChecks.interval_append test 41472 41728 41984
  (FiniteChecks.interval_append test 41472 41600 41728
  checked_41472
  checked_41600)
  (FiniteChecks.interval_append test 41728 41856 41984
  checked_41728
  checked_41856)))
  (FiniteChecks.interval_append test 41984 42496 43008
  (FiniteChecks.interval_append test 41984 42240 42496
  (FiniteChecks.interval_append test 41984 42112 42240
  checked_41984
  checked_42112)
  (FiniteChecks.interval_append test 42240 42368 42496
  checked_42240
  checked_42368))
  (FiniteChecks.interval_append test 42496 42752 43008
  (FiniteChecks.interval_append test 42496 42624 42752
  checked_42496
  checked_42624)
  (FiniteChecks.interval_append test 42752 42880 43008
  checked_42752
  checked_42880))))
  (FiniteChecks.interval_append test 43008 44032 45056
  (FiniteChecks.interval_append test 43008 43520 44032
  (FiniteChecks.interval_append test 43008 43264 43520
  (FiniteChecks.interval_append test 43008 43136 43264
  checked_43008
  checked_43136)
  (FiniteChecks.interval_append test 43264 43392 43520
  checked_43264
  checked_43392))
  (FiniteChecks.interval_append test 43520 43776 44032
  (FiniteChecks.interval_append test 43520 43648 43776
  checked_43520
  checked_43648)
  (FiniteChecks.interval_append test 43776 43904 44032
  checked_43776
  checked_43904)))
  (FiniteChecks.interval_append test 44032 44544 45056
  (FiniteChecks.interval_append test 44032 44288 44544
  (FiniteChecks.interval_append test 44032 44160 44288
  checked_44032
  checked_44160)
  (FiniteChecks.interval_append test 44288 44416 44544
  checked_44288
  checked_44416))
  (FiniteChecks.interval_append test 44544 44800 45056
  (FiniteChecks.interval_append test 44544 44672 44800
  checked_44544
  checked_44672)
  (FiniteChecks.interval_append test 44800 44928 45056
  checked_44800
  checked_44928)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
