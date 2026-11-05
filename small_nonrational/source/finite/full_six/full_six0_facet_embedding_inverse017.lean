module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_034816 : Interval inverseTest 34816 34944 :=
  interval_of_check inverseTest 34816 128 (by decide +kernel)

theorem inverse_034944 : Interval inverseTest 34944 35072 :=
  interval_of_check inverseTest 34944 128 (by decide +kernel)

theorem inverse_035072 : Interval inverseTest 35072 35200 :=
  interval_of_check inverseTest 35072 128 (by decide +kernel)

theorem inverse_035200 : Interval inverseTest 35200 35328 :=
  interval_of_check inverseTest 35200 128 (by decide +kernel)

theorem inverse_035328 : Interval inverseTest 35328 35456 :=
  interval_of_check inverseTest 35328 128 (by decide +kernel)

theorem inverse_035456 : Interval inverseTest 35456 35584 :=
  interval_of_check inverseTest 35456 128 (by decide +kernel)

theorem inverse_035584 : Interval inverseTest 35584 35712 :=
  interval_of_check inverseTest 35584 128 (by decide +kernel)

theorem inverse_035712 : Interval inverseTest 35712 35840 :=
  interval_of_check inverseTest 35712 128 (by decide +kernel)

theorem inverse_035840 : Interval inverseTest 35840 35968 :=
  interval_of_check inverseTest 35840 128 (by decide +kernel)

theorem inverse_035968 : Interval inverseTest 35968 36096 :=
  interval_of_check inverseTest 35968 128 (by decide +kernel)

theorem inverse_036096 : Interval inverseTest 36096 36224 :=
  interval_of_check inverseTest 36096 128 (by decide +kernel)

theorem inverse_036224 : Interval inverseTest 36224 36352 :=
  interval_of_check inverseTest 36224 128 (by decide +kernel)

theorem inverse_036352 : Interval inverseTest 36352 36480 :=
  interval_of_check inverseTest 36352 128 (by decide +kernel)

theorem inverse_036480 : Interval inverseTest 36480 36608 :=
  interval_of_check inverseTest 36480 128 (by decide +kernel)

theorem inverse_036608 : Interval inverseTest 36608 36736 :=
  interval_of_check inverseTest 36608 128 (by decide +kernel)

theorem inverse_036736 : Interval inverseTest 36736 36864 :=
  interval_of_check inverseTest 36736 128 (by decide +kernel)

theorem inverse_join_034816_035072 : Interval inverseTest 34816 35072 :=
  interval_append inverseTest 34816 34944 35072 inverse_034816 inverse_034944

theorem inverse_join_035072_035328 : Interval inverseTest 35072 35328 :=
  interval_append inverseTest 35072 35200 35328 inverse_035072 inverse_035200

theorem inverse_join_034816_035328 : Interval inverseTest 34816 35328 :=
  interval_append inverseTest 34816 35072 35328 inverse_join_034816_035072 inverse_join_035072_035328

theorem inverse_join_035328_035584 : Interval inverseTest 35328 35584 :=
  interval_append inverseTest 35328 35456 35584 inverse_035328 inverse_035456

theorem inverse_join_035584_035840 : Interval inverseTest 35584 35840 :=
  interval_append inverseTest 35584 35712 35840 inverse_035584 inverse_035712

theorem inverse_join_035328_035840 : Interval inverseTest 35328 35840 :=
  interval_append inverseTest 35328 35584 35840 inverse_join_035328_035584 inverse_join_035584_035840

theorem inverse_join_034816_035840 : Interval inverseTest 34816 35840 :=
  interval_append inverseTest 34816 35328 35840 inverse_join_034816_035328 inverse_join_035328_035840

theorem inverse_join_035840_036096 : Interval inverseTest 35840 36096 :=
  interval_append inverseTest 35840 35968 36096 inverse_035840 inverse_035968

theorem inverse_join_036096_036352 : Interval inverseTest 36096 36352 :=
  interval_append inverseTest 36096 36224 36352 inverse_036096 inverse_036224

theorem inverse_join_035840_036352 : Interval inverseTest 35840 36352 :=
  interval_append inverseTest 35840 36096 36352 inverse_join_035840_036096 inverse_join_036096_036352

theorem inverse_join_036352_036608 : Interval inverseTest 36352 36608 :=
  interval_append inverseTest 36352 36480 36608 inverse_036352 inverse_036480

theorem inverse_join_036608_036864 : Interval inverseTest 36608 36864 :=
  interval_append inverseTest 36608 36736 36864 inverse_036608 inverse_036736

theorem inverse_join_036352_036864 : Interval inverseTest 36352 36864 :=
  interval_append inverseTest 36352 36608 36864 inverse_join_036352_036608 inverse_join_036608_036864

theorem inverse_join_035840_036864 : Interval inverseTest 35840 36864 :=
  interval_append inverseTest 35840 36352 36864 inverse_join_035840_036352 inverse_join_036352_036864

theorem inverse_join_034816_036864 : Interval inverseTest 34816 36864 :=
  interval_append inverseTest 34816 35840 36864 inverse_join_034816_035840 inverse_join_035840_036864

theorem inverse_part_017 : Interval inverseTest 34816 36864 := inverse_join_034816_036864
end Papers.RationalityTen.FullSix0FacetEmbedding
