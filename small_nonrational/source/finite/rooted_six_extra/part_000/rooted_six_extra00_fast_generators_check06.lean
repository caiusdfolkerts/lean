module
prelude
public import RootedSixExtra00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_24576 : FiniteChecks.Interval test 24576 24704 :=
  FiniteChecks.interval_of_check test 24576 128 (by decide +kernel)
theorem checked_24704 : FiniteChecks.Interval test 24704 24832 :=
  FiniteChecks.interval_of_check test 24704 128 (by decide +kernel)
theorem checked_24832 : FiniteChecks.Interval test 24832 24960 :=
  FiniteChecks.interval_of_check test 24832 128 (by decide +kernel)
theorem checked_24960 : FiniteChecks.Interval test 24960 25088 :=
  FiniteChecks.interval_of_check test 24960 128 (by decide +kernel)
theorem checked_25088 : FiniteChecks.Interval test 25088 25216 :=
  FiniteChecks.interval_of_check test 25088 128 (by decide +kernel)
theorem checked_25216 : FiniteChecks.Interval test 25216 25344 :=
  FiniteChecks.interval_of_check test 25216 128 (by decide +kernel)
theorem checked_25344 : FiniteChecks.Interval test 25344 25472 :=
  FiniteChecks.interval_of_check test 25344 128 (by decide +kernel)
theorem checked_25472 : FiniteChecks.Interval test 25472 25600 :=
  FiniteChecks.interval_of_check test 25472 128 (by decide +kernel)
theorem checked_25600 : FiniteChecks.Interval test 25600 25728 :=
  FiniteChecks.interval_of_check test 25600 128 (by decide +kernel)
theorem checked_25728 : FiniteChecks.Interval test 25728 25856 :=
  FiniteChecks.interval_of_check test 25728 128 (by decide +kernel)
theorem checked_25856 : FiniteChecks.Interval test 25856 25984 :=
  FiniteChecks.interval_of_check test 25856 128 (by decide +kernel)
theorem checked_25984 : FiniteChecks.Interval test 25984 26112 :=
  FiniteChecks.interval_of_check test 25984 128 (by decide +kernel)
theorem checked_26112 : FiniteChecks.Interval test 26112 26240 :=
  FiniteChecks.interval_of_check test 26112 128 (by decide +kernel)
theorem checked_26240 : FiniteChecks.Interval test 26240 26368 :=
  FiniteChecks.interval_of_check test 26240 128 (by decide +kernel)
theorem checked_26368 : FiniteChecks.Interval test 26368 26496 :=
  FiniteChecks.interval_of_check test 26368 128 (by decide +kernel)
theorem checked_26496 : FiniteChecks.Interval test 26496 26624 :=
  FiniteChecks.interval_of_check test 26496 128 (by decide +kernel)
theorem checked_26624 : FiniteChecks.Interval test 26624 26752 :=
  FiniteChecks.interval_of_check test 26624 128 (by decide +kernel)
theorem checked_26752 : FiniteChecks.Interval test 26752 26880 :=
  FiniteChecks.interval_of_check test 26752 128 (by decide +kernel)
theorem checked_26880 : FiniteChecks.Interval test 26880 27008 :=
  FiniteChecks.interval_of_check test 26880 128 (by decide +kernel)
theorem checked_27008 : FiniteChecks.Interval test 27008 27136 :=
  FiniteChecks.interval_of_check test 27008 128 (by decide +kernel)
theorem checked_27136 : FiniteChecks.Interval test 27136 27264 :=
  FiniteChecks.interval_of_check test 27136 128 (by decide +kernel)
theorem checked_27264 : FiniteChecks.Interval test 27264 27392 :=
  FiniteChecks.interval_of_check test 27264 128 (by decide +kernel)
theorem checked_27392 : FiniteChecks.Interval test 27392 27520 :=
  FiniteChecks.interval_of_check test 27392 128 (by decide +kernel)
theorem checked_27520 : FiniteChecks.Interval test 27520 27648 :=
  FiniteChecks.interval_of_check test 27520 128 (by decide +kernel)
theorem checked_27648 : FiniteChecks.Interval test 27648 27776 :=
  FiniteChecks.interval_of_check test 27648 128 (by decide +kernel)
theorem checked_27776 : FiniteChecks.Interval test 27776 27904 :=
  FiniteChecks.interval_of_check test 27776 128 (by decide +kernel)
theorem checked_27904 : FiniteChecks.Interval test 27904 28032 :=
  FiniteChecks.interval_of_check test 27904 128 (by decide +kernel)
theorem checked_28032 : FiniteChecks.Interval test 28032 28160 :=
  FiniteChecks.interval_of_check test 28032 128 (by decide +kernel)
theorem checked_28160 : FiniteChecks.Interval test 28160 28288 :=
  FiniteChecks.interval_of_check test 28160 128 (by decide +kernel)
theorem checked_28288 : FiniteChecks.Interval test 28288 28416 :=
  FiniteChecks.interval_of_check test 28288 128 (by decide +kernel)
theorem checked_28416 : FiniteChecks.Interval test 28416 28544 :=
  FiniteChecks.interval_of_check test 28416 128 (by decide +kernel)
theorem checked_28544 : FiniteChecks.Interval test 28544 28672 :=
  FiniteChecks.interval_of_check test 28544 128 (by decide +kernel)
theorem interval_24576 : FiniteChecks.Interval test 24576 28672 :=
  (FiniteChecks.interval_append test 24576 26624 28672
  (FiniteChecks.interval_append test 24576 25600 26624
  (FiniteChecks.interval_append test 24576 25088 25600
  (FiniteChecks.interval_append test 24576 24832 25088
  (FiniteChecks.interval_append test 24576 24704 24832
  checked_24576
  checked_24704)
  (FiniteChecks.interval_append test 24832 24960 25088
  checked_24832
  checked_24960))
  (FiniteChecks.interval_append test 25088 25344 25600
  (FiniteChecks.interval_append test 25088 25216 25344
  checked_25088
  checked_25216)
  (FiniteChecks.interval_append test 25344 25472 25600
  checked_25344
  checked_25472)))
  (FiniteChecks.interval_append test 25600 26112 26624
  (FiniteChecks.interval_append test 25600 25856 26112
  (FiniteChecks.interval_append test 25600 25728 25856
  checked_25600
  checked_25728)
  (FiniteChecks.interval_append test 25856 25984 26112
  checked_25856
  checked_25984))
  (FiniteChecks.interval_append test 26112 26368 26624
  (FiniteChecks.interval_append test 26112 26240 26368
  checked_26112
  checked_26240)
  (FiniteChecks.interval_append test 26368 26496 26624
  checked_26368
  checked_26496))))
  (FiniteChecks.interval_append test 26624 27648 28672
  (FiniteChecks.interval_append test 26624 27136 27648
  (FiniteChecks.interval_append test 26624 26880 27136
  (FiniteChecks.interval_append test 26624 26752 26880
  checked_26624
  checked_26752)
  (FiniteChecks.interval_append test 26880 27008 27136
  checked_26880
  checked_27008))
  (FiniteChecks.interval_append test 27136 27392 27648
  (FiniteChecks.interval_append test 27136 27264 27392
  checked_27136
  checked_27264)
  (FiniteChecks.interval_append test 27392 27520 27648
  checked_27392
  checked_27520)))
  (FiniteChecks.interval_append test 27648 28160 28672
  (FiniteChecks.interval_append test 27648 27904 28160
  (FiniteChecks.interval_append test 27648 27776 27904
  checked_27648
  checked_27776)
  (FiniteChecks.interval_append test 27904 28032 28160
  checked_27904
  checked_28032))
  (FiniteChecks.interval_append test 28160 28416 28672
  (FiniteChecks.interval_append test 28160 28288 28416
  checked_28160
  checked_28288)
  (FiniteChecks.interval_append test 28416 28544 28672
  checked_28416
  checked_28544)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
