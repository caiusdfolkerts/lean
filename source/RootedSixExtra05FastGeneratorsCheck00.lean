module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 0 128 128
cert_checked_9 128 256 128
cert_checked_9 256 384 128
cert_checked_9 384 512 128
cert_checked_9 512 640 128
cert_checked_9 640 768 128
cert_checked_9 768 896 128
cert_checked_9 896 1024 128
cert_checked_9 1024 1152 128
cert_checked_9 1152 1280 128
cert_checked_9 1280 1408 128
cert_checked_9 1408 1536 128
cert_checked_9 1536 1664 128
cert_checked_9 1664 1792 128
cert_checked_9 1792 1920 128
cert_checked_9 1920 2048 128
cert_checked_9 2048 2176 128
cert_checked_9 2176 2304 128
cert_checked_9 2304 2432 128
cert_checked_9 2432 2560 128
cert_checked_9 2560 2688 128
cert_checked_9 2688 2816 128
cert_checked_9 2816 2944 128
cert_checked_9 2944 3072 128
cert_checked_9 3072 3200 128
cert_checked_9 3200 3328 128
cert_checked_9 3328 3456 128
cert_checked_9 3456 3584 128
cert_checked_9 3584 3712 128
cert_checked_9 3712 3840 128
cert_checked_9 3840 3968 128
cert_checked_9 3968 4096 128
theorem interval_0 : FiniteChecks.Interval test 0 4096 :=
  (FiniteChecks.interval_append test 0 2048 4096
  (FiniteChecks.interval_append test 0 1024 2048
  (FiniteChecks.interval_append test 0 512 1024
  (FiniteChecks.interval_append test 0 256 512
  (FiniteChecks.interval_append test 0 128 256
  checked_0
  checked_128)
  (FiniteChecks.interval_append test 256 384 512
  checked_256
  checked_384))
  (FiniteChecks.interval_append test 512 768 1024
  (FiniteChecks.interval_append test 512 640 768
  checked_512
  checked_640)
  (FiniteChecks.interval_append test 768 896 1024
  checked_768
  checked_896)))
  (FiniteChecks.interval_append test 1024 1536 2048
  (FiniteChecks.interval_append test 1024 1280 1536
  (FiniteChecks.interval_append test 1024 1152 1280
  checked_1024
  checked_1152)
  (FiniteChecks.interval_append test 1280 1408 1536
  checked_1280
  checked_1408))
  (FiniteChecks.interval_append test 1536 1792 2048
  (FiniteChecks.interval_append test 1536 1664 1792
  checked_1536
  checked_1664)
  (FiniteChecks.interval_append test 1792 1920 2048
  checked_1792
  checked_1920))))
  (FiniteChecks.interval_append test 2048 3072 4096
  (FiniteChecks.interval_append test 2048 2560 3072
  (FiniteChecks.interval_append test 2048 2304 2560
  (FiniteChecks.interval_append test 2048 2176 2304
  checked_2048
  checked_2176)
  (FiniteChecks.interval_append test 2304 2432 2560
  checked_2304
  checked_2432))
  (FiniteChecks.interval_append test 2560 2816 3072
  (FiniteChecks.interval_append test 2560 2688 2816
  checked_2560
  checked_2688)
  (FiniteChecks.interval_append test 2816 2944 3072
  checked_2816
  checked_2944)))
  (FiniteChecks.interval_append test 3072 3584 4096
  (FiniteChecks.interval_append test 3072 3328 3584
  (FiniteChecks.interval_append test 3072 3200 3328
  checked_3072
  checked_3200)
  (FiniteChecks.interval_append test 3328 3456 3584
  checked_3328
  checked_3456))
  (FiniteChecks.interval_append test 3584 3840 4096
  (FiniteChecks.interval_append test 3584 3712 3840
  checked_3584
  checked_3712)
  (FiniteChecks.interval_append test 3840 3968 4096
  checked_3840
  checked_3968)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast
