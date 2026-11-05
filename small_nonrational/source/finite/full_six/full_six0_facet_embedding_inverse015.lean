module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_030720 : Interval inverseTest 30720 30848 :=
  interval_of_check inverseTest 30720 128 (by decide +kernel)

theorem inverse_030848 : Interval inverseTest 30848 30976 :=
  interval_of_check inverseTest 30848 128 (by decide +kernel)

theorem inverse_030976 : Interval inverseTest 30976 31104 :=
  interval_of_check inverseTest 30976 128 (by decide +kernel)

theorem inverse_031104 : Interval inverseTest 31104 31232 :=
  interval_of_check inverseTest 31104 128 (by decide +kernel)

theorem inverse_031232 : Interval inverseTest 31232 31360 :=
  interval_of_check inverseTest 31232 128 (by decide +kernel)

theorem inverse_031360 : Interval inverseTest 31360 31488 :=
  interval_of_check inverseTest 31360 128 (by decide +kernel)

theorem inverse_031488 : Interval inverseTest 31488 31616 :=
  interval_of_check inverseTest 31488 128 (by decide +kernel)

theorem inverse_031616 : Interval inverseTest 31616 31744 :=
  interval_of_check inverseTest 31616 128 (by decide +kernel)

theorem inverse_031744 : Interval inverseTest 31744 31872 :=
  interval_of_check inverseTest 31744 128 (by decide +kernel)

theorem inverse_031872 : Interval inverseTest 31872 32000 :=
  interval_of_check inverseTest 31872 128 (by decide +kernel)

theorem inverse_032000 : Interval inverseTest 32000 32128 :=
  interval_of_check inverseTest 32000 128 (by decide +kernel)

theorem inverse_032128 : Interval inverseTest 32128 32256 :=
  interval_of_check inverseTest 32128 128 (by decide +kernel)

theorem inverse_032256 : Interval inverseTest 32256 32384 :=
  interval_of_check inverseTest 32256 128 (by decide +kernel)

theorem inverse_032384 : Interval inverseTest 32384 32512 :=
  interval_of_check inverseTest 32384 128 (by decide +kernel)

theorem inverse_032512 : Interval inverseTest 32512 32640 :=
  interval_of_check inverseTest 32512 128 (by decide +kernel)

theorem inverse_032640 : Interval inverseTest 32640 32768 :=
  interval_of_check inverseTest 32640 128 (by decide +kernel)

theorem inverse_join_030720_030976 : Interval inverseTest 30720 30976 :=
  interval_append inverseTest 30720 30848 30976 inverse_030720 inverse_030848

theorem inverse_join_030976_031232 : Interval inverseTest 30976 31232 :=
  interval_append inverseTest 30976 31104 31232 inverse_030976 inverse_031104

theorem inverse_join_030720_031232 : Interval inverseTest 30720 31232 :=
  interval_append inverseTest 30720 30976 31232 inverse_join_030720_030976 inverse_join_030976_031232

theorem inverse_join_031232_031488 : Interval inverseTest 31232 31488 :=
  interval_append inverseTest 31232 31360 31488 inverse_031232 inverse_031360

theorem inverse_join_031488_031744 : Interval inverseTest 31488 31744 :=
  interval_append inverseTest 31488 31616 31744 inverse_031488 inverse_031616

theorem inverse_join_031232_031744 : Interval inverseTest 31232 31744 :=
  interval_append inverseTest 31232 31488 31744 inverse_join_031232_031488 inverse_join_031488_031744

theorem inverse_join_030720_031744 : Interval inverseTest 30720 31744 :=
  interval_append inverseTest 30720 31232 31744 inverse_join_030720_031232 inverse_join_031232_031744

theorem inverse_join_031744_032000 : Interval inverseTest 31744 32000 :=
  interval_append inverseTest 31744 31872 32000 inverse_031744 inverse_031872

theorem inverse_join_032000_032256 : Interval inverseTest 32000 32256 :=
  interval_append inverseTest 32000 32128 32256 inverse_032000 inverse_032128

theorem inverse_join_031744_032256 : Interval inverseTest 31744 32256 :=
  interval_append inverseTest 31744 32000 32256 inverse_join_031744_032000 inverse_join_032000_032256

theorem inverse_join_032256_032512 : Interval inverseTest 32256 32512 :=
  interval_append inverseTest 32256 32384 32512 inverse_032256 inverse_032384

theorem inverse_join_032512_032768 : Interval inverseTest 32512 32768 :=
  interval_append inverseTest 32512 32640 32768 inverse_032512 inverse_032640

theorem inverse_join_032256_032768 : Interval inverseTest 32256 32768 :=
  interval_append inverseTest 32256 32512 32768 inverse_join_032256_032512 inverse_join_032512_032768

theorem inverse_join_031744_032768 : Interval inverseTest 31744 32768 :=
  interval_append inverseTest 31744 32256 32768 inverse_join_031744_032256 inverse_join_032256_032768

theorem inverse_join_030720_032768 : Interval inverseTest 30720 32768 :=
  interval_append inverseTest 30720 31744 32768 inverse_join_030720_031744 inverse_join_031744_032768

theorem inverse_part_015 : Interval inverseTest 30720 32768 := inverse_join_030720_032768
end Papers.RationalityTen.FullSix0FacetEmbedding
