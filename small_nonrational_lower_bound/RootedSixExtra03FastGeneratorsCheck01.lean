module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra03FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 4096 4224 128
cert_checked_9 4224 4352 128
cert_checked_9 4352 4480 128
cert_checked_9 4480 4608 128
cert_checked_9 4608 4736 128
cert_checked_9 4736 4864 128
cert_checked_9 4864 4992 128
cert_checked_9 4992 5120 128
cert_checked_9 5120 5248 128
cert_checked_9 5248 5376 128
cert_checked_9 5376 5504 128
cert_checked_9 5504 5632 128
cert_checked_9 5632 5760 128
cert_checked_9 5760 5888 128
cert_checked_9 5888 6016 128
cert_checked_9 6016 6144 128
cert_checked_9 6144 6272 128
cert_checked_9 6272 6400 128
cert_checked_9 6400 6528 128
cert_checked_9 6528 6656 128
cert_checked_9 6656 6784 128
cert_checked_9 6784 6912 128
cert_checked_9 6912 7040 128
cert_checked_9 7040 7168 128
cert_checked_9 7168 7296 128
cert_checked_9 7296 7424 128
cert_checked_9 7424 7552 128
cert_checked_9 7552 7680 128
cert_checked_9 7680 7808 128
cert_checked_9 7808 7936 128
cert_checked_9 7936 8064 128
cert_checked_9 8064 8192 128
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
end Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.Fast
