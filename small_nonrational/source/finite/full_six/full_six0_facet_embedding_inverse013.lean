module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_026624 : Interval inverseTest 26624 26752 :=
  interval_of_check inverseTest 26624 128 (by decide +kernel)

theorem inverse_026752 : Interval inverseTest 26752 26880 :=
  interval_of_check inverseTest 26752 128 (by decide +kernel)

theorem inverse_026880 : Interval inverseTest 26880 27008 :=
  interval_of_check inverseTest 26880 128 (by decide +kernel)

theorem inverse_027008 : Interval inverseTest 27008 27136 :=
  interval_of_check inverseTest 27008 128 (by decide +kernel)

theorem inverse_027136 : Interval inverseTest 27136 27264 :=
  interval_of_check inverseTest 27136 128 (by decide +kernel)

theorem inverse_027264 : Interval inverseTest 27264 27392 :=
  interval_of_check inverseTest 27264 128 (by decide +kernel)

theorem inverse_027392 : Interval inverseTest 27392 27520 :=
  interval_of_check inverseTest 27392 128 (by decide +kernel)

theorem inverse_027520 : Interval inverseTest 27520 27648 :=
  interval_of_check inverseTest 27520 128 (by decide +kernel)

theorem inverse_027648 : Interval inverseTest 27648 27776 :=
  interval_of_check inverseTest 27648 128 (by decide +kernel)

theorem inverse_027776 : Interval inverseTest 27776 27904 :=
  interval_of_check inverseTest 27776 128 (by decide +kernel)

theorem inverse_027904 : Interval inverseTest 27904 28032 :=
  interval_of_check inverseTest 27904 128 (by decide +kernel)

theorem inverse_028032 : Interval inverseTest 28032 28160 :=
  interval_of_check inverseTest 28032 128 (by decide +kernel)

theorem inverse_028160 : Interval inverseTest 28160 28288 :=
  interval_of_check inverseTest 28160 128 (by decide +kernel)

theorem inverse_028288 : Interval inverseTest 28288 28416 :=
  interval_of_check inverseTest 28288 128 (by decide +kernel)

theorem inverse_028416 : Interval inverseTest 28416 28544 :=
  interval_of_check inverseTest 28416 128 (by decide +kernel)

theorem inverse_028544 : Interval inverseTest 28544 28672 :=
  interval_of_check inverseTest 28544 128 (by decide +kernel)

theorem inverse_join_026624_026880 : Interval inverseTest 26624 26880 :=
  interval_append inverseTest 26624 26752 26880 inverse_026624 inverse_026752

theorem inverse_join_026880_027136 : Interval inverseTest 26880 27136 :=
  interval_append inverseTest 26880 27008 27136 inverse_026880 inverse_027008

theorem inverse_join_026624_027136 : Interval inverseTest 26624 27136 :=
  interval_append inverseTest 26624 26880 27136 inverse_join_026624_026880 inverse_join_026880_027136

theorem inverse_join_027136_027392 : Interval inverseTest 27136 27392 :=
  interval_append inverseTest 27136 27264 27392 inverse_027136 inverse_027264

theorem inverse_join_027392_027648 : Interval inverseTest 27392 27648 :=
  interval_append inverseTest 27392 27520 27648 inverse_027392 inverse_027520

theorem inverse_join_027136_027648 : Interval inverseTest 27136 27648 :=
  interval_append inverseTest 27136 27392 27648 inverse_join_027136_027392 inverse_join_027392_027648

theorem inverse_join_026624_027648 : Interval inverseTest 26624 27648 :=
  interval_append inverseTest 26624 27136 27648 inverse_join_026624_027136 inverse_join_027136_027648

theorem inverse_join_027648_027904 : Interval inverseTest 27648 27904 :=
  interval_append inverseTest 27648 27776 27904 inverse_027648 inverse_027776

theorem inverse_join_027904_028160 : Interval inverseTest 27904 28160 :=
  interval_append inverseTest 27904 28032 28160 inverse_027904 inverse_028032

theorem inverse_join_027648_028160 : Interval inverseTest 27648 28160 :=
  interval_append inverseTest 27648 27904 28160 inverse_join_027648_027904 inverse_join_027904_028160

theorem inverse_join_028160_028416 : Interval inverseTest 28160 28416 :=
  interval_append inverseTest 28160 28288 28416 inverse_028160 inverse_028288

theorem inverse_join_028416_028672 : Interval inverseTest 28416 28672 :=
  interval_append inverseTest 28416 28544 28672 inverse_028416 inverse_028544

theorem inverse_join_028160_028672 : Interval inverseTest 28160 28672 :=
  interval_append inverseTest 28160 28416 28672 inverse_join_028160_028416 inverse_join_028416_028672

theorem inverse_join_027648_028672 : Interval inverseTest 27648 28672 :=
  interval_append inverseTest 27648 28160 28672 inverse_join_027648_028160 inverse_join_028160_028672

theorem inverse_join_026624_028672 : Interval inverseTest 26624 28672 :=
  interval_append inverseTest 26624 27648 28672 inverse_join_026624_027648 inverse_join_027648_028672

theorem inverse_part_013 : Interval inverseTest 26624 28672 := inverse_join_026624_028672
end Papers.RationalityTen.FullSix0FacetEmbedding
