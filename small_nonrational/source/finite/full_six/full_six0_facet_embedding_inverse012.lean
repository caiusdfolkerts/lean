module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_024576 : Interval inverseTest 24576 24704 :=
  interval_of_check inverseTest 24576 128 (by decide +kernel)

theorem inverse_024704 : Interval inverseTest 24704 24832 :=
  interval_of_check inverseTest 24704 128 (by decide +kernel)

theorem inverse_024832 : Interval inverseTest 24832 24960 :=
  interval_of_check inverseTest 24832 128 (by decide +kernel)

theorem inverse_024960 : Interval inverseTest 24960 25088 :=
  interval_of_check inverseTest 24960 128 (by decide +kernel)

theorem inverse_025088 : Interval inverseTest 25088 25216 :=
  interval_of_check inverseTest 25088 128 (by decide +kernel)

theorem inverse_025216 : Interval inverseTest 25216 25344 :=
  interval_of_check inverseTest 25216 128 (by decide +kernel)

theorem inverse_025344 : Interval inverseTest 25344 25472 :=
  interval_of_check inverseTest 25344 128 (by decide +kernel)

theorem inverse_025472 : Interval inverseTest 25472 25600 :=
  interval_of_check inverseTest 25472 128 (by decide +kernel)

theorem inverse_025600 : Interval inverseTest 25600 25728 :=
  interval_of_check inverseTest 25600 128 (by decide +kernel)

theorem inverse_025728 : Interval inverseTest 25728 25856 :=
  interval_of_check inverseTest 25728 128 (by decide +kernel)

theorem inverse_025856 : Interval inverseTest 25856 25984 :=
  interval_of_check inverseTest 25856 128 (by decide +kernel)

theorem inverse_025984 : Interval inverseTest 25984 26112 :=
  interval_of_check inverseTest 25984 128 (by decide +kernel)

theorem inverse_026112 : Interval inverseTest 26112 26240 :=
  interval_of_check inverseTest 26112 128 (by decide +kernel)

theorem inverse_026240 : Interval inverseTest 26240 26368 :=
  interval_of_check inverseTest 26240 128 (by decide +kernel)

theorem inverse_026368 : Interval inverseTest 26368 26496 :=
  interval_of_check inverseTest 26368 128 (by decide +kernel)

theorem inverse_026496 : Interval inverseTest 26496 26624 :=
  interval_of_check inverseTest 26496 128 (by decide +kernel)

theorem inverse_join_024576_024832 : Interval inverseTest 24576 24832 :=
  interval_append inverseTest 24576 24704 24832 inverse_024576 inverse_024704

theorem inverse_join_024832_025088 : Interval inverseTest 24832 25088 :=
  interval_append inverseTest 24832 24960 25088 inverse_024832 inverse_024960

theorem inverse_join_024576_025088 : Interval inverseTest 24576 25088 :=
  interval_append inverseTest 24576 24832 25088 inverse_join_024576_024832 inverse_join_024832_025088

theorem inverse_join_025088_025344 : Interval inverseTest 25088 25344 :=
  interval_append inverseTest 25088 25216 25344 inverse_025088 inverse_025216

theorem inverse_join_025344_025600 : Interval inverseTest 25344 25600 :=
  interval_append inverseTest 25344 25472 25600 inverse_025344 inverse_025472

theorem inverse_join_025088_025600 : Interval inverseTest 25088 25600 :=
  interval_append inverseTest 25088 25344 25600 inverse_join_025088_025344 inverse_join_025344_025600

theorem inverse_join_024576_025600 : Interval inverseTest 24576 25600 :=
  interval_append inverseTest 24576 25088 25600 inverse_join_024576_025088 inverse_join_025088_025600

theorem inverse_join_025600_025856 : Interval inverseTest 25600 25856 :=
  interval_append inverseTest 25600 25728 25856 inverse_025600 inverse_025728

theorem inverse_join_025856_026112 : Interval inverseTest 25856 26112 :=
  interval_append inverseTest 25856 25984 26112 inverse_025856 inverse_025984

theorem inverse_join_025600_026112 : Interval inverseTest 25600 26112 :=
  interval_append inverseTest 25600 25856 26112 inverse_join_025600_025856 inverse_join_025856_026112

theorem inverse_join_026112_026368 : Interval inverseTest 26112 26368 :=
  interval_append inverseTest 26112 26240 26368 inverse_026112 inverse_026240

theorem inverse_join_026368_026624 : Interval inverseTest 26368 26624 :=
  interval_append inverseTest 26368 26496 26624 inverse_026368 inverse_026496

theorem inverse_join_026112_026624 : Interval inverseTest 26112 26624 :=
  interval_append inverseTest 26112 26368 26624 inverse_join_026112_026368 inverse_join_026368_026624

theorem inverse_join_025600_026624 : Interval inverseTest 25600 26624 :=
  interval_append inverseTest 25600 26112 26624 inverse_join_025600_026112 inverse_join_026112_026624

theorem inverse_join_024576_026624 : Interval inverseTest 24576 26624 :=
  interval_append inverseTest 24576 25600 26624 inverse_join_024576_025600 inverse_join_025600_026624

theorem inverse_part_012 : Interval inverseTest 24576 26624 := inverse_join_024576_026624
end Papers.RationalityTen.FullSix0FacetEmbedding
