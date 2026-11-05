module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_006144 : Interval inverseTest 6144 6272 :=
  interval_of_check inverseTest 6144 128 (by decide +kernel)

theorem inverse_006272 : Interval inverseTest 6272 6400 :=
  interval_of_check inverseTest 6272 128 (by decide +kernel)

theorem inverse_006400 : Interval inverseTest 6400 6528 :=
  interval_of_check inverseTest 6400 128 (by decide +kernel)

theorem inverse_006528 : Interval inverseTest 6528 6656 :=
  interval_of_check inverseTest 6528 128 (by decide +kernel)

theorem inverse_006656 : Interval inverseTest 6656 6784 :=
  interval_of_check inverseTest 6656 128 (by decide +kernel)

theorem inverse_006784 : Interval inverseTest 6784 6912 :=
  interval_of_check inverseTest 6784 128 (by decide +kernel)

theorem inverse_006912 : Interval inverseTest 6912 7040 :=
  interval_of_check inverseTest 6912 128 (by decide +kernel)

theorem inverse_007040 : Interval inverseTest 7040 7168 :=
  interval_of_check inverseTest 7040 128 (by decide +kernel)

theorem inverse_007168 : Interval inverseTest 7168 7296 :=
  interval_of_check inverseTest 7168 128 (by decide +kernel)

theorem inverse_007296 : Interval inverseTest 7296 7424 :=
  interval_of_check inverseTest 7296 128 (by decide +kernel)

theorem inverse_007424 : Interval inverseTest 7424 7552 :=
  interval_of_check inverseTest 7424 128 (by decide +kernel)

theorem inverse_007552 : Interval inverseTest 7552 7680 :=
  interval_of_check inverseTest 7552 128 (by decide +kernel)

theorem inverse_007680 : Interval inverseTest 7680 7808 :=
  interval_of_check inverseTest 7680 128 (by decide +kernel)

theorem inverse_007808 : Interval inverseTest 7808 7936 :=
  interval_of_check inverseTest 7808 128 (by decide +kernel)

theorem inverse_007936 : Interval inverseTest 7936 8064 :=
  interval_of_check inverseTest 7936 128 (by decide +kernel)

theorem inverse_008064 : Interval inverseTest 8064 8192 :=
  interval_of_check inverseTest 8064 128 (by decide +kernel)

theorem inverse_join_006144_006400 : Interval inverseTest 6144 6400 :=
  interval_append inverseTest 6144 6272 6400 inverse_006144 inverse_006272

theorem inverse_join_006400_006656 : Interval inverseTest 6400 6656 :=
  interval_append inverseTest 6400 6528 6656 inverse_006400 inverse_006528

theorem inverse_join_006144_006656 : Interval inverseTest 6144 6656 :=
  interval_append inverseTest 6144 6400 6656 inverse_join_006144_006400 inverse_join_006400_006656

theorem inverse_join_006656_006912 : Interval inverseTest 6656 6912 :=
  interval_append inverseTest 6656 6784 6912 inverse_006656 inverse_006784

theorem inverse_join_006912_007168 : Interval inverseTest 6912 7168 :=
  interval_append inverseTest 6912 7040 7168 inverse_006912 inverse_007040

theorem inverse_join_006656_007168 : Interval inverseTest 6656 7168 :=
  interval_append inverseTest 6656 6912 7168 inverse_join_006656_006912 inverse_join_006912_007168

theorem inverse_join_006144_007168 : Interval inverseTest 6144 7168 :=
  interval_append inverseTest 6144 6656 7168 inverse_join_006144_006656 inverse_join_006656_007168

theorem inverse_join_007168_007424 : Interval inverseTest 7168 7424 :=
  interval_append inverseTest 7168 7296 7424 inverse_007168 inverse_007296

theorem inverse_join_007424_007680 : Interval inverseTest 7424 7680 :=
  interval_append inverseTest 7424 7552 7680 inverse_007424 inverse_007552

theorem inverse_join_007168_007680 : Interval inverseTest 7168 7680 :=
  interval_append inverseTest 7168 7424 7680 inverse_join_007168_007424 inverse_join_007424_007680

theorem inverse_join_007680_007936 : Interval inverseTest 7680 7936 :=
  interval_append inverseTest 7680 7808 7936 inverse_007680 inverse_007808

theorem inverse_join_007936_008192 : Interval inverseTest 7936 8192 :=
  interval_append inverseTest 7936 8064 8192 inverse_007936 inverse_008064

theorem inverse_join_007680_008192 : Interval inverseTest 7680 8192 :=
  interval_append inverseTest 7680 7936 8192 inverse_join_007680_007936 inverse_join_007936_008192

theorem inverse_join_007168_008192 : Interval inverseTest 7168 8192 :=
  interval_append inverseTest 7168 7680 8192 inverse_join_007168_007680 inverse_join_007680_008192

theorem inverse_join_006144_008192 : Interval inverseTest 6144 8192 :=
  interval_append inverseTest 6144 7168 8192 inverse_join_006144_007168 inverse_join_007168_008192

theorem inverse_part_003 : Interval inverseTest 6144 8192 := inverse_join_006144_008192
end Papers.RationalityTen.FullSix0FacetEmbedding
