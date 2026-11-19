module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 40960 41088 128
cert_checked_9 41088 41216 128
cert_checked_9 41216 41344 128
cert_checked_9 41344 41472 128
cert_checked_9 41472 41600 128
cert_checked_9 41600 41728 128
cert_checked_9 41728 41856 128
cert_checked_9 41856 41984 128
cert_checked_9 41984 42112 128
cert_checked_9 42112 42240 128
cert_checked_9 42240 42368 128
cert_checked_9 42368 42496 128
cert_checked_9 42496 42624 128
cert_checked_9 42624 42752 128
cert_checked_9 42752 42880 128
cert_checked_9 42880 43008 128
cert_checked_9 43008 43136 128
cert_checked_9 43136 43264 128
cert_checked_9 43264 43392 128
cert_checked_9 43392 43520 128
cert_checked_9 43520 43648 128
cert_checked_9 43648 43776 128
cert_checked_9 43776 43904 128
cert_checked_9 43904 44032 128
cert_checked_9 44032 44120 88
theorem interval_40960 : FiniteChecks.Interval test 40960 44120 :=
  (FiniteChecks.interval_append test 40960 42496 44120
  (FiniteChecks.interval_append test 40960 41728 42496
  (FiniteChecks.interval_append test 40960 41344 41728
  (FiniteChecks.interval_append test 40960 41088 41344
  checked_40960
  (FiniteChecks.interval_append test 41088 41216 41344
  checked_41088
  checked_41216))
  (FiniteChecks.interval_append test 41344 41472 41728
  checked_41344
  (FiniteChecks.interval_append test 41472 41600 41728
  checked_41472
  checked_41600)))
  (FiniteChecks.interval_append test 41728 42112 42496
  (FiniteChecks.interval_append test 41728 41856 42112
  checked_41728
  (FiniteChecks.interval_append test 41856 41984 42112
  checked_41856
  checked_41984))
  (FiniteChecks.interval_append test 42112 42240 42496
  checked_42112
  (FiniteChecks.interval_append test 42240 42368 42496
  checked_42240
  checked_42368))))
  (FiniteChecks.interval_append test 42496 43264 44120
  (FiniteChecks.interval_append test 42496 42880 43264
  (FiniteChecks.interval_append test 42496 42624 42880
  checked_42496
  (FiniteChecks.interval_append test 42624 42752 42880
  checked_42624
  checked_42752))
  (FiniteChecks.interval_append test 42880 43008 43264
  checked_42880
  (FiniteChecks.interval_append test 43008 43136 43264
  checked_43008
  checked_43136)))
  (FiniteChecks.interval_append test 43264 43648 44120
  (FiniteChecks.interval_append test 43264 43392 43648
  checked_43264
  (FiniteChecks.interval_append test 43392 43520 43648
  checked_43392
  checked_43520))
  (FiniteChecks.interval_append test 43648 43904 44120
  (FiniteChecks.interval_append test 43648 43776 43904
  checked_43648
  checked_43776)
  (FiniteChecks.interval_append test 43904 44032 44120
  checked_43904
  checked_44032)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
