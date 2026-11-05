module
prelude
public import RootedSixExtra01FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_4096 : FiniteChecks.Interval test 4096 4224 :=
  FiniteChecks.interval_of_check test 4096 128 (by decide +kernel)
theorem checked_4224 : FiniteChecks.Interval test 4224 4352 :=
  FiniteChecks.interval_of_check test 4224 128 (by decide +kernel)
theorem checked_4352 : FiniteChecks.Interval test 4352 4480 :=
  FiniteChecks.interval_of_check test 4352 128 (by decide +kernel)
theorem checked_4480 : FiniteChecks.Interval test 4480 4608 :=
  FiniteChecks.interval_of_check test 4480 128 (by decide +kernel)
theorem checked_4608 : FiniteChecks.Interval test 4608 4736 :=
  FiniteChecks.interval_of_check test 4608 128 (by decide +kernel)
theorem checked_4736 : FiniteChecks.Interval test 4736 4864 :=
  FiniteChecks.interval_of_check test 4736 128 (by decide +kernel)
theorem checked_4864 : FiniteChecks.Interval test 4864 4992 :=
  FiniteChecks.interval_of_check test 4864 128 (by decide +kernel)
theorem checked_4992 : FiniteChecks.Interval test 4992 5120 :=
  FiniteChecks.interval_of_check test 4992 128 (by decide +kernel)
theorem checked_5120 : FiniteChecks.Interval test 5120 5248 :=
  FiniteChecks.interval_of_check test 5120 128 (by decide +kernel)
theorem checked_5248 : FiniteChecks.Interval test 5248 5376 :=
  FiniteChecks.interval_of_check test 5248 128 (by decide +kernel)
theorem checked_5376 : FiniteChecks.Interval test 5376 5504 :=
  FiniteChecks.interval_of_check test 5376 128 (by decide +kernel)
theorem checked_5504 : FiniteChecks.Interval test 5504 5632 :=
  FiniteChecks.interval_of_check test 5504 128 (by decide +kernel)
theorem checked_5632 : FiniteChecks.Interval test 5632 5760 :=
  FiniteChecks.interval_of_check test 5632 128 (by decide +kernel)
theorem checked_5760 : FiniteChecks.Interval test 5760 5888 :=
  FiniteChecks.interval_of_check test 5760 128 (by decide +kernel)
theorem checked_5888 : FiniteChecks.Interval test 5888 6016 :=
  FiniteChecks.interval_of_check test 5888 128 (by decide +kernel)
theorem checked_6016 : FiniteChecks.Interval test 6016 6144 :=
  FiniteChecks.interval_of_check test 6016 128 (by decide +kernel)
theorem checked_6144 : FiniteChecks.Interval test 6144 6272 :=
  FiniteChecks.interval_of_check test 6144 128 (by decide +kernel)
theorem checked_6272 : FiniteChecks.Interval test 6272 6400 :=
  FiniteChecks.interval_of_check test 6272 128 (by decide +kernel)
theorem checked_6400 : FiniteChecks.Interval test 6400 6528 :=
  FiniteChecks.interval_of_check test 6400 128 (by decide +kernel)
theorem checked_6528 : FiniteChecks.Interval test 6528 6656 :=
  FiniteChecks.interval_of_check test 6528 128 (by decide +kernel)
theorem checked_6656 : FiniteChecks.Interval test 6656 6784 :=
  FiniteChecks.interval_of_check test 6656 128 (by decide +kernel)
theorem checked_6784 : FiniteChecks.Interval test 6784 6912 :=
  FiniteChecks.interval_of_check test 6784 128 (by decide +kernel)
theorem checked_6912 : FiniteChecks.Interval test 6912 7040 :=
  FiniteChecks.interval_of_check test 6912 128 (by decide +kernel)
theorem checked_7040 : FiniteChecks.Interval test 7040 7168 :=
  FiniteChecks.interval_of_check test 7040 128 (by decide +kernel)
theorem checked_7168 : FiniteChecks.Interval test 7168 7296 :=
  FiniteChecks.interval_of_check test 7168 128 (by decide +kernel)
theorem checked_7296 : FiniteChecks.Interval test 7296 7424 :=
  FiniteChecks.interval_of_check test 7296 128 (by decide +kernel)
theorem checked_7424 : FiniteChecks.Interval test 7424 7552 :=
  FiniteChecks.interval_of_check test 7424 128 (by decide +kernel)
theorem checked_7552 : FiniteChecks.Interval test 7552 7680 :=
  FiniteChecks.interval_of_check test 7552 128 (by decide +kernel)
theorem checked_7680 : FiniteChecks.Interval test 7680 7808 :=
  FiniteChecks.interval_of_check test 7680 128 (by decide +kernel)
theorem checked_7808 : FiniteChecks.Interval test 7808 7936 :=
  FiniteChecks.interval_of_check test 7808 128 (by decide +kernel)
theorem checked_7936 : FiniteChecks.Interval test 7936 8064 :=
  FiniteChecks.interval_of_check test 7936 128 (by decide +kernel)
theorem checked_8064 : FiniteChecks.Interval test 8064 8192 :=
  FiniteChecks.interval_of_check test 8064 128 (by decide +kernel)
theorem interval_4096 : FiniteChecks.Interval test 4096 8192 :=
  (FiniteChecks.interval_append test 4096 6144 8192
  (FiniteChecks.interval_append test 4096 5120 6144
  (FiniteChecks.interval_append test 4096 4608 5120
  (FiniteChecks.interval_append test 4096 4352 4608
  (FiniteChecks.interval_append test 4096 4224 4352
  checked_4096
  checked_4224)
  (FiniteChecks.interval_append test 4352 4480 4608
  checked_4352
  checked_4480))
  (FiniteChecks.interval_append test 4608 4864 5120
  (FiniteChecks.interval_append test 4608 4736 4864
  checked_4608
  checked_4736)
  (FiniteChecks.interval_append test 4864 4992 5120
  checked_4864
  checked_4992)))
  (FiniteChecks.interval_append test 5120 5632 6144
  (FiniteChecks.interval_append test 5120 5376 5632
  (FiniteChecks.interval_append test 5120 5248 5376
  checked_5120
  checked_5248)
  (FiniteChecks.interval_append test 5376 5504 5632
  checked_5376
  checked_5504))
  (FiniteChecks.interval_append test 5632 5888 6144
  (FiniteChecks.interval_append test 5632 5760 5888
  checked_5632
  checked_5760)
  (FiniteChecks.interval_append test 5888 6016 6144
  checked_5888
  checked_6016))))
  (FiniteChecks.interval_append test 6144 7168 8192
  (FiniteChecks.interval_append test 6144 6656 7168
  (FiniteChecks.interval_append test 6144 6400 6656
  (FiniteChecks.interval_append test 6144 6272 6400
  checked_6144
  checked_6272)
  (FiniteChecks.interval_append test 6400 6528 6656
  checked_6400
  checked_6528))
  (FiniteChecks.interval_append test 6656 6912 7168
  (FiniteChecks.interval_append test 6656 6784 6912
  checked_6656
  checked_6784)
  (FiniteChecks.interval_append test 6912 7040 7168
  checked_6912
  checked_7040)))
  (FiniteChecks.interval_append test 7168 7680 8192
  (FiniteChecks.interval_append test 7168 7424 7680
  (FiniteChecks.interval_append test 7168 7296 7424
  checked_7168
  checked_7296)
  (FiniteChecks.interval_append test 7424 7552 7680
  checked_7424
  checked_7552))
  (FiniteChecks.interval_append test 7680 7936 8192
  (FiniteChecks.interval_append test 7680 7808 7936
  checked_7680
  checked_7808)
  (FiniteChecks.interval_append test 7936 8064 8192
  checked_7936
  checked_8064)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast
