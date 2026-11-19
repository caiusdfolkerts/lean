module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 102400 102528 128
cert_checked_7 102528 102656 128
cert_checked_7 102656 102784 128
cert_checked_7 102784 102912 128
cert_checked_7 102912 103040 128
cert_checked_7 103040 103168 128
cert_checked_7 103168 103296 128
cert_checked_7 103296 103424 128
cert_checked_7 103424 103552 128
cert_checked_7 103552 103680 128
cert_checked_7 103680 103808 128
cert_checked_7 103808 103936 128
cert_checked_7 103936 104064 128
cert_checked_7 104064 104192 128
cert_checked_7 104192 104320 128
cert_checked_7 104320 104448 128
cert_checked_7 104448 104576 128
cert_checked_7 104576 104704 128
cert_checked_7 104704 104832 128
cert_checked_7 104832 104960 128
cert_checked_7 104960 105088 128
cert_checked_7 105088 105216 128
cert_checked_7 105216 105344 128
cert_checked_7 105344 105472 128
cert_checked_7 105472 105600 128
cert_checked_7 105600 105728 128
cert_checked_7 105728 105856 128
cert_checked_7 105856 105984 128
cert_checked_7 105984 106112 128
cert_checked_7 106112 106240 128
cert_checked_7 106240 106368 128
cert_checked_7 106368 106496 128
theorem interval_102400 : FiniteChecks.Interval test 102400 106496 :=
  (FiniteChecks.interval_append test 102400 104448 106496
  (FiniteChecks.interval_append test 102400 103424 104448
  (FiniteChecks.interval_append test 102400 102912 103424
  (FiniteChecks.interval_append test 102400 102656 102912
  (FiniteChecks.interval_append test 102400 102528 102656
  checked_102400
  checked_102528)
  (FiniteChecks.interval_append test 102656 102784 102912
  checked_102656
  checked_102784))
  (FiniteChecks.interval_append test 102912 103168 103424
  (FiniteChecks.interval_append test 102912 103040 103168
  checked_102912
  checked_103040)
  (FiniteChecks.interval_append test 103168 103296 103424
  checked_103168
  checked_103296)))
  (FiniteChecks.interval_append test 103424 103936 104448
  (FiniteChecks.interval_append test 103424 103680 103936
  (FiniteChecks.interval_append test 103424 103552 103680
  checked_103424
  checked_103552)
  (FiniteChecks.interval_append test 103680 103808 103936
  checked_103680
  checked_103808))
  (FiniteChecks.interval_append test 103936 104192 104448
  (FiniteChecks.interval_append test 103936 104064 104192
  checked_103936
  checked_104064)
  (FiniteChecks.interval_append test 104192 104320 104448
  checked_104192
  checked_104320))))
  (FiniteChecks.interval_append test 104448 105472 106496
  (FiniteChecks.interval_append test 104448 104960 105472
  (FiniteChecks.interval_append test 104448 104704 104960
  (FiniteChecks.interval_append test 104448 104576 104704
  checked_104448
  checked_104576)
  (FiniteChecks.interval_append test 104704 104832 104960
  checked_104704
  checked_104832))
  (FiniteChecks.interval_append test 104960 105216 105472
  (FiniteChecks.interval_append test 104960 105088 105216
  checked_104960
  checked_105088)
  (FiniteChecks.interval_append test 105216 105344 105472
  checked_105216
  checked_105344)))
  (FiniteChecks.interval_append test 105472 105984 106496
  (FiniteChecks.interval_append test 105472 105728 105984
  (FiniteChecks.interval_append test 105472 105600 105728
  checked_105472
  checked_105600)
  (FiniteChecks.interval_append test 105728 105856 105984
  checked_105728
  checked_105856))
  (FiniteChecks.interval_append test 105984 106240 106496
  (FiniteChecks.interval_append test 105984 106112 106240
  checked_105984
  checked_106112)
  (FiniteChecks.interval_append test 106240 106368 106496
  checked_106240
  checked_106368)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
