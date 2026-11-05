module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_022528 : Interval inverseTest 22528 22656 :=
  interval_of_check inverseTest 22528 128 (by decide +kernel)

theorem inverse_022656 : Interval inverseTest 22656 22784 :=
  interval_of_check inverseTest 22656 128 (by decide +kernel)

theorem inverse_022784 : Interval inverseTest 22784 22912 :=
  interval_of_check inverseTest 22784 128 (by decide +kernel)

theorem inverse_022912 : Interval inverseTest 22912 23040 :=
  interval_of_check inverseTest 22912 128 (by decide +kernel)

theorem inverse_023040 : Interval inverseTest 23040 23168 :=
  interval_of_check inverseTest 23040 128 (by decide +kernel)

theorem inverse_023168 : Interval inverseTest 23168 23296 :=
  interval_of_check inverseTest 23168 128 (by decide +kernel)

theorem inverse_023296 : Interval inverseTest 23296 23424 :=
  interval_of_check inverseTest 23296 128 (by decide +kernel)

theorem inverse_023424 : Interval inverseTest 23424 23552 :=
  interval_of_check inverseTest 23424 128 (by decide +kernel)

theorem inverse_023552 : Interval inverseTest 23552 23680 :=
  interval_of_check inverseTest 23552 128 (by decide +kernel)

theorem inverse_023680 : Interval inverseTest 23680 23808 :=
  interval_of_check inverseTest 23680 128 (by decide +kernel)

theorem inverse_023808 : Interval inverseTest 23808 23936 :=
  interval_of_check inverseTest 23808 128 (by decide +kernel)

theorem inverse_023936 : Interval inverseTest 23936 24064 :=
  interval_of_check inverseTest 23936 128 (by decide +kernel)

theorem inverse_024064 : Interval inverseTest 24064 24192 :=
  interval_of_check inverseTest 24064 128 (by decide +kernel)

theorem inverse_024192 : Interval inverseTest 24192 24320 :=
  interval_of_check inverseTest 24192 128 (by decide +kernel)

theorem inverse_024320 : Interval inverseTest 24320 24448 :=
  interval_of_check inverseTest 24320 128 (by decide +kernel)

theorem inverse_024448 : Interval inverseTest 24448 24576 :=
  interval_of_check inverseTest 24448 128 (by decide +kernel)

theorem inverse_join_022528_022784 : Interval inverseTest 22528 22784 :=
  interval_append inverseTest 22528 22656 22784 inverse_022528 inverse_022656

theorem inverse_join_022784_023040 : Interval inverseTest 22784 23040 :=
  interval_append inverseTest 22784 22912 23040 inverse_022784 inverse_022912

theorem inverse_join_022528_023040 : Interval inverseTest 22528 23040 :=
  interval_append inverseTest 22528 22784 23040 inverse_join_022528_022784 inverse_join_022784_023040

theorem inverse_join_023040_023296 : Interval inverseTest 23040 23296 :=
  interval_append inverseTest 23040 23168 23296 inverse_023040 inverse_023168

theorem inverse_join_023296_023552 : Interval inverseTest 23296 23552 :=
  interval_append inverseTest 23296 23424 23552 inverse_023296 inverse_023424

theorem inverse_join_023040_023552 : Interval inverseTest 23040 23552 :=
  interval_append inverseTest 23040 23296 23552 inverse_join_023040_023296 inverse_join_023296_023552

theorem inverse_join_022528_023552 : Interval inverseTest 22528 23552 :=
  interval_append inverseTest 22528 23040 23552 inverse_join_022528_023040 inverse_join_023040_023552

theorem inverse_join_023552_023808 : Interval inverseTest 23552 23808 :=
  interval_append inverseTest 23552 23680 23808 inverse_023552 inverse_023680

theorem inverse_join_023808_024064 : Interval inverseTest 23808 24064 :=
  interval_append inverseTest 23808 23936 24064 inverse_023808 inverse_023936

theorem inverse_join_023552_024064 : Interval inverseTest 23552 24064 :=
  interval_append inverseTest 23552 23808 24064 inverse_join_023552_023808 inverse_join_023808_024064

theorem inverse_join_024064_024320 : Interval inverseTest 24064 24320 :=
  interval_append inverseTest 24064 24192 24320 inverse_024064 inverse_024192

theorem inverse_join_024320_024576 : Interval inverseTest 24320 24576 :=
  interval_append inverseTest 24320 24448 24576 inverse_024320 inverse_024448

theorem inverse_join_024064_024576 : Interval inverseTest 24064 24576 :=
  interval_append inverseTest 24064 24320 24576 inverse_join_024064_024320 inverse_join_024320_024576

theorem inverse_join_023552_024576 : Interval inverseTest 23552 24576 :=
  interval_append inverseTest 23552 24064 24576 inverse_join_023552_024064 inverse_join_024064_024576

theorem inverse_join_022528_024576 : Interval inverseTest 22528 24576 :=
  interval_append inverseTest 22528 23552 24576 inverse_join_022528_023552 inverse_join_023552_024576

theorem inverse_part_011 : Interval inverseTest 22528 24576 := inverse_join_022528_024576
end Papers.RationalityTen.FullSix0FacetEmbedding
