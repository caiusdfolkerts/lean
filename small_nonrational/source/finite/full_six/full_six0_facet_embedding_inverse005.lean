module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_010240 : Interval inverseTest 10240 10368 :=
  interval_of_check inverseTest 10240 128 (by decide +kernel)

theorem inverse_010368 : Interval inverseTest 10368 10496 :=
  interval_of_check inverseTest 10368 128 (by decide +kernel)

theorem inverse_010496 : Interval inverseTest 10496 10624 :=
  interval_of_check inverseTest 10496 128 (by decide +kernel)

theorem inverse_010624 : Interval inverseTest 10624 10752 :=
  interval_of_check inverseTest 10624 128 (by decide +kernel)

theorem inverse_010752 : Interval inverseTest 10752 10880 :=
  interval_of_check inverseTest 10752 128 (by decide +kernel)

theorem inverse_010880 : Interval inverseTest 10880 11008 :=
  interval_of_check inverseTest 10880 128 (by decide +kernel)

theorem inverse_011008 : Interval inverseTest 11008 11136 :=
  interval_of_check inverseTest 11008 128 (by decide +kernel)

theorem inverse_011136 : Interval inverseTest 11136 11264 :=
  interval_of_check inverseTest 11136 128 (by decide +kernel)

theorem inverse_011264 : Interval inverseTest 11264 11392 :=
  interval_of_check inverseTest 11264 128 (by decide +kernel)

theorem inverse_011392 : Interval inverseTest 11392 11520 :=
  interval_of_check inverseTest 11392 128 (by decide +kernel)

theorem inverse_011520 : Interval inverseTest 11520 11648 :=
  interval_of_check inverseTest 11520 128 (by decide +kernel)

theorem inverse_011648 : Interval inverseTest 11648 11776 :=
  interval_of_check inverseTest 11648 128 (by decide +kernel)

theorem inverse_011776 : Interval inverseTest 11776 11904 :=
  interval_of_check inverseTest 11776 128 (by decide +kernel)

theorem inverse_011904 : Interval inverseTest 11904 12032 :=
  interval_of_check inverseTest 11904 128 (by decide +kernel)

theorem inverse_012032 : Interval inverseTest 12032 12160 :=
  interval_of_check inverseTest 12032 128 (by decide +kernel)

theorem inverse_012160 : Interval inverseTest 12160 12288 :=
  interval_of_check inverseTest 12160 128 (by decide +kernel)

theorem inverse_join_010240_010496 : Interval inverseTest 10240 10496 :=
  interval_append inverseTest 10240 10368 10496 inverse_010240 inverse_010368

theorem inverse_join_010496_010752 : Interval inverseTest 10496 10752 :=
  interval_append inverseTest 10496 10624 10752 inverse_010496 inverse_010624

theorem inverse_join_010240_010752 : Interval inverseTest 10240 10752 :=
  interval_append inverseTest 10240 10496 10752 inverse_join_010240_010496 inverse_join_010496_010752

theorem inverse_join_010752_011008 : Interval inverseTest 10752 11008 :=
  interval_append inverseTest 10752 10880 11008 inverse_010752 inverse_010880

theorem inverse_join_011008_011264 : Interval inverseTest 11008 11264 :=
  interval_append inverseTest 11008 11136 11264 inverse_011008 inverse_011136

theorem inverse_join_010752_011264 : Interval inverseTest 10752 11264 :=
  interval_append inverseTest 10752 11008 11264 inverse_join_010752_011008 inverse_join_011008_011264

theorem inverse_join_010240_011264 : Interval inverseTest 10240 11264 :=
  interval_append inverseTest 10240 10752 11264 inverse_join_010240_010752 inverse_join_010752_011264

theorem inverse_join_011264_011520 : Interval inverseTest 11264 11520 :=
  interval_append inverseTest 11264 11392 11520 inverse_011264 inverse_011392

theorem inverse_join_011520_011776 : Interval inverseTest 11520 11776 :=
  interval_append inverseTest 11520 11648 11776 inverse_011520 inverse_011648

theorem inverse_join_011264_011776 : Interval inverseTest 11264 11776 :=
  interval_append inverseTest 11264 11520 11776 inverse_join_011264_011520 inverse_join_011520_011776

theorem inverse_join_011776_012032 : Interval inverseTest 11776 12032 :=
  interval_append inverseTest 11776 11904 12032 inverse_011776 inverse_011904

theorem inverse_join_012032_012288 : Interval inverseTest 12032 12288 :=
  interval_append inverseTest 12032 12160 12288 inverse_012032 inverse_012160

theorem inverse_join_011776_012288 : Interval inverseTest 11776 12288 :=
  interval_append inverseTest 11776 12032 12288 inverse_join_011776_012032 inverse_join_012032_012288

theorem inverse_join_011264_012288 : Interval inverseTest 11264 12288 :=
  interval_append inverseTest 11264 11776 12288 inverse_join_011264_011776 inverse_join_011776_012288

theorem inverse_join_010240_012288 : Interval inverseTest 10240 12288 :=
  interval_append inverseTest 10240 11264 12288 inverse_join_010240_011264 inverse_join_011264_012288

theorem inverse_part_005 : Interval inverseTest 10240 12288 := inverse_join_010240_012288
end Papers.RationalityTen.FullSix0FacetEmbedding
