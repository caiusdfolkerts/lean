module
prelude
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_77824 : FiniteChecks.Interval test 77824 77952 :=
  FiniteChecks.interval_of_check test 77824 128 (by decide +kernel)
theorem checked_77952 : FiniteChecks.Interval test 77952 78080 :=
  FiniteChecks.interval_of_check test 77952 128 (by decide +kernel)
theorem checked_78080 : FiniteChecks.Interval test 78080 78208 :=
  FiniteChecks.interval_of_check test 78080 128 (by decide +kernel)
theorem checked_78208 : FiniteChecks.Interval test 78208 78336 :=
  FiniteChecks.interval_of_check test 78208 128 (by decide +kernel)
theorem checked_78336 : FiniteChecks.Interval test 78336 78464 :=
  FiniteChecks.interval_of_check test 78336 128 (by decide +kernel)
theorem checked_78464 : FiniteChecks.Interval test 78464 78592 :=
  FiniteChecks.interval_of_check test 78464 128 (by decide +kernel)
theorem checked_78592 : FiniteChecks.Interval test 78592 78720 :=
  FiniteChecks.interval_of_check test 78592 128 (by decide +kernel)
theorem checked_78720 : FiniteChecks.Interval test 78720 78848 :=
  FiniteChecks.interval_of_check test 78720 128 (by decide +kernel)
theorem checked_78848 : FiniteChecks.Interval test 78848 78976 :=
  FiniteChecks.interval_of_check test 78848 128 (by decide +kernel)
theorem checked_78976 : FiniteChecks.Interval test 78976 79104 :=
  FiniteChecks.interval_of_check test 78976 128 (by decide +kernel)
theorem checked_79104 : FiniteChecks.Interval test 79104 79232 :=
  FiniteChecks.interval_of_check test 79104 128 (by decide +kernel)
theorem checked_79232 : FiniteChecks.Interval test 79232 79360 :=
  FiniteChecks.interval_of_check test 79232 128 (by decide +kernel)
theorem checked_79360 : FiniteChecks.Interval test 79360 79488 :=
  FiniteChecks.interval_of_check test 79360 128 (by decide +kernel)
theorem checked_79488 : FiniteChecks.Interval test 79488 79616 :=
  FiniteChecks.interval_of_check test 79488 128 (by decide +kernel)
theorem checked_79616 : FiniteChecks.Interval test 79616 79744 :=
  FiniteChecks.interval_of_check test 79616 128 (by decide +kernel)
theorem checked_79744 : FiniteChecks.Interval test 79744 79872 :=
  FiniteChecks.interval_of_check test 79744 128 (by decide +kernel)
theorem checked_79872 : FiniteChecks.Interval test 79872 80000 :=
  FiniteChecks.interval_of_check test 79872 128 (by decide +kernel)
theorem checked_80000 : FiniteChecks.Interval test 80000 80128 :=
  FiniteChecks.interval_of_check test 80000 128 (by decide +kernel)
theorem checked_80128 : FiniteChecks.Interval test 80128 80256 :=
  FiniteChecks.interval_of_check test 80128 128 (by decide +kernel)
theorem checked_80256 : FiniteChecks.Interval test 80256 80384 :=
  FiniteChecks.interval_of_check test 80256 128 (by decide +kernel)
theorem checked_80384 : FiniteChecks.Interval test 80384 80512 :=
  FiniteChecks.interval_of_check test 80384 128 (by decide +kernel)
theorem checked_80512 : FiniteChecks.Interval test 80512 80640 :=
  FiniteChecks.interval_of_check test 80512 128 (by decide +kernel)
theorem checked_80640 : FiniteChecks.Interval test 80640 80768 :=
  FiniteChecks.interval_of_check test 80640 128 (by decide +kernel)
theorem checked_80768 : FiniteChecks.Interval test 80768 80896 :=
  FiniteChecks.interval_of_check test 80768 128 (by decide +kernel)
theorem checked_80896 : FiniteChecks.Interval test 80896 81024 :=
  FiniteChecks.interval_of_check test 80896 128 (by decide +kernel)
theorem checked_81024 : FiniteChecks.Interval test 81024 81152 :=
  FiniteChecks.interval_of_check test 81024 128 (by decide +kernel)
theorem checked_81152 : FiniteChecks.Interval test 81152 81280 :=
  FiniteChecks.interval_of_check test 81152 128 (by decide +kernel)
theorem checked_81280 : FiniteChecks.Interval test 81280 81408 :=
  FiniteChecks.interval_of_check test 81280 128 (by decide +kernel)
theorem checked_81408 : FiniteChecks.Interval test 81408 81536 :=
  FiniteChecks.interval_of_check test 81408 128 (by decide +kernel)
theorem checked_81536 : FiniteChecks.Interval test 81536 81664 :=
  FiniteChecks.interval_of_check test 81536 128 (by decide +kernel)
theorem checked_81664 : FiniteChecks.Interval test 81664 81792 :=
  FiniteChecks.interval_of_check test 81664 128 (by decide +kernel)
theorem checked_81792 : FiniteChecks.Interval test 81792 81920 :=
  FiniteChecks.interval_of_check test 81792 128 (by decide +kernel)
theorem interval_77824 : FiniteChecks.Interval test 77824 81920 :=
  (FiniteChecks.interval_append test 77824 79872 81920
  (FiniteChecks.interval_append test 77824 78848 79872
  (FiniteChecks.interval_append test 77824 78336 78848
  (FiniteChecks.interval_append test 77824 78080 78336
  (FiniteChecks.interval_append test 77824 77952 78080
  checked_77824
  checked_77952)
  (FiniteChecks.interval_append test 78080 78208 78336
  checked_78080
  checked_78208))
  (FiniteChecks.interval_append test 78336 78592 78848
  (FiniteChecks.interval_append test 78336 78464 78592
  checked_78336
  checked_78464)
  (FiniteChecks.interval_append test 78592 78720 78848
  checked_78592
  checked_78720)))
  (FiniteChecks.interval_append test 78848 79360 79872
  (FiniteChecks.interval_append test 78848 79104 79360
  (FiniteChecks.interval_append test 78848 78976 79104
  checked_78848
  checked_78976)
  (FiniteChecks.interval_append test 79104 79232 79360
  checked_79104
  checked_79232))
  (FiniteChecks.interval_append test 79360 79616 79872
  (FiniteChecks.interval_append test 79360 79488 79616
  checked_79360
  checked_79488)
  (FiniteChecks.interval_append test 79616 79744 79872
  checked_79616
  checked_79744))))
  (FiniteChecks.interval_append test 79872 80896 81920
  (FiniteChecks.interval_append test 79872 80384 80896
  (FiniteChecks.interval_append test 79872 80128 80384
  (FiniteChecks.interval_append test 79872 80000 80128
  checked_79872
  checked_80000)
  (FiniteChecks.interval_append test 80128 80256 80384
  checked_80128
  checked_80256))
  (FiniteChecks.interval_append test 80384 80640 80896
  (FiniteChecks.interval_append test 80384 80512 80640
  checked_80384
  checked_80512)
  (FiniteChecks.interval_append test 80640 80768 80896
  checked_80640
  checked_80768)))
  (FiniteChecks.interval_append test 80896 81408 81920
  (FiniteChecks.interval_append test 80896 81152 81408
  (FiniteChecks.interval_append test 80896 81024 81152
  checked_80896
  checked_81024)
  (FiniteChecks.interval_append test 81152 81280 81408
  checked_81152
  checked_81280))
  (FiniteChecks.interval_append test 81408 81664 81920
  (FiniteChecks.interval_append test 81408 81536 81664
  checked_81408
  checked_81536)
  (FiniteChecks.interval_append test 81664 81792 81920
  checked_81664
  checked_81792)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
