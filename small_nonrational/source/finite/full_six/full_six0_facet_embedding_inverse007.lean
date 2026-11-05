module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_014336 : Interval inverseTest 14336 14464 :=
  interval_of_check inverseTest 14336 128 (by decide +kernel)

theorem inverse_014464 : Interval inverseTest 14464 14592 :=
  interval_of_check inverseTest 14464 128 (by decide +kernel)

theorem inverse_014592 : Interval inverseTest 14592 14720 :=
  interval_of_check inverseTest 14592 128 (by decide +kernel)

theorem inverse_014720 : Interval inverseTest 14720 14848 :=
  interval_of_check inverseTest 14720 128 (by decide +kernel)

theorem inverse_014848 : Interval inverseTest 14848 14976 :=
  interval_of_check inverseTest 14848 128 (by decide +kernel)

theorem inverse_014976 : Interval inverseTest 14976 15104 :=
  interval_of_check inverseTest 14976 128 (by decide +kernel)

theorem inverse_015104 : Interval inverseTest 15104 15232 :=
  interval_of_check inverseTest 15104 128 (by decide +kernel)

theorem inverse_015232 : Interval inverseTest 15232 15360 :=
  interval_of_check inverseTest 15232 128 (by decide +kernel)

theorem inverse_015360 : Interval inverseTest 15360 15488 :=
  interval_of_check inverseTest 15360 128 (by decide +kernel)

theorem inverse_015488 : Interval inverseTest 15488 15616 :=
  interval_of_check inverseTest 15488 128 (by decide +kernel)

theorem inverse_015616 : Interval inverseTest 15616 15744 :=
  interval_of_check inverseTest 15616 128 (by decide +kernel)

theorem inverse_015744 : Interval inverseTest 15744 15872 :=
  interval_of_check inverseTest 15744 128 (by decide +kernel)

theorem inverse_015872 : Interval inverseTest 15872 16000 :=
  interval_of_check inverseTest 15872 128 (by decide +kernel)

theorem inverse_016000 : Interval inverseTest 16000 16128 :=
  interval_of_check inverseTest 16000 128 (by decide +kernel)

theorem inverse_016128 : Interval inverseTest 16128 16256 :=
  interval_of_check inverseTest 16128 128 (by decide +kernel)

theorem inverse_016256 : Interval inverseTest 16256 16384 :=
  interval_of_check inverseTest 16256 128 (by decide +kernel)

theorem inverse_join_014336_014592 : Interval inverseTest 14336 14592 :=
  interval_append inverseTest 14336 14464 14592 inverse_014336 inverse_014464

theorem inverse_join_014592_014848 : Interval inverseTest 14592 14848 :=
  interval_append inverseTest 14592 14720 14848 inverse_014592 inverse_014720

theorem inverse_join_014336_014848 : Interval inverseTest 14336 14848 :=
  interval_append inverseTest 14336 14592 14848 inverse_join_014336_014592 inverse_join_014592_014848

theorem inverse_join_014848_015104 : Interval inverseTest 14848 15104 :=
  interval_append inverseTest 14848 14976 15104 inverse_014848 inverse_014976

theorem inverse_join_015104_015360 : Interval inverseTest 15104 15360 :=
  interval_append inverseTest 15104 15232 15360 inverse_015104 inverse_015232

theorem inverse_join_014848_015360 : Interval inverseTest 14848 15360 :=
  interval_append inverseTest 14848 15104 15360 inverse_join_014848_015104 inverse_join_015104_015360

theorem inverse_join_014336_015360 : Interval inverseTest 14336 15360 :=
  interval_append inverseTest 14336 14848 15360 inverse_join_014336_014848 inverse_join_014848_015360

theorem inverse_join_015360_015616 : Interval inverseTest 15360 15616 :=
  interval_append inverseTest 15360 15488 15616 inverse_015360 inverse_015488

theorem inverse_join_015616_015872 : Interval inverseTest 15616 15872 :=
  interval_append inverseTest 15616 15744 15872 inverse_015616 inverse_015744

theorem inverse_join_015360_015872 : Interval inverseTest 15360 15872 :=
  interval_append inverseTest 15360 15616 15872 inverse_join_015360_015616 inverse_join_015616_015872

theorem inverse_join_015872_016128 : Interval inverseTest 15872 16128 :=
  interval_append inverseTest 15872 16000 16128 inverse_015872 inverse_016000

theorem inverse_join_016128_016384 : Interval inverseTest 16128 16384 :=
  interval_append inverseTest 16128 16256 16384 inverse_016128 inverse_016256

theorem inverse_join_015872_016384 : Interval inverseTest 15872 16384 :=
  interval_append inverseTest 15872 16128 16384 inverse_join_015872_016128 inverse_join_016128_016384

theorem inverse_join_015360_016384 : Interval inverseTest 15360 16384 :=
  interval_append inverseTest 15360 15872 16384 inverse_join_015360_015872 inverse_join_015872_016384

theorem inverse_join_014336_016384 : Interval inverseTest 14336 16384 :=
  interval_append inverseTest 14336 15360 16384 inverse_join_014336_015360 inverse_join_015360_016384

theorem inverse_part_007 : Interval inverseTest 14336 16384 := inverse_join_014336_016384
end Papers.RationalityTen.FullSix0FacetEmbedding
