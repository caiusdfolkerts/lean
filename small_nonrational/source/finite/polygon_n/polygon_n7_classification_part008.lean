module

public import PolygonN7ClassificationPart007

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_02928 : FiniteChecks.Interval terminalTest 2928 2936 :=
  FiniteChecks.interval_of_check terminalTest 2928 8 (by decide +kernel)

theorem terminal_data_02936 : FiniteChecks.Interval terminalTest 2936 2944 :=
  FiniteChecks.interval_of_check terminalTest 2936 8 (by decide +kernel)

theorem terminal_data_02944 : FiniteChecks.Interval terminalTest 2944 2952 :=
  FiniteChecks.interval_of_check terminalTest 2944 8 (by decide +kernel)

theorem terminal_data_02952 : FiniteChecks.Interval terminalTest 2952 2960 :=
  FiniteChecks.interval_of_check terminalTest 2952 8 (by decide +kernel)

theorem terminal_data_02960 : FiniteChecks.Interval terminalTest 2960 2968 :=
  FiniteChecks.interval_of_check terminalTest 2960 8 (by decide +kernel)

theorem terminal_data_02968 : FiniteChecks.Interval terminalTest 2968 2976 :=
  FiniteChecks.interval_of_check terminalTest 2968 8 (by decide +kernel)

theorem terminal_data_02976 : FiniteChecks.Interval terminalTest 2976 2984 :=
  FiniteChecks.interval_of_check terminalTest 2976 8 (by decide +kernel)

theorem terminal_data_02984 : FiniteChecks.Interval terminalTest 2984 2992 :=
  FiniteChecks.interval_of_check terminalTest 2984 8 (by decide +kernel)

theorem terminal_data_02992 : FiniteChecks.Interval terminalTest 2992 3000 :=
  FiniteChecks.interval_of_check terminalTest 2992 8 (by decide +kernel)

theorem terminal_data_03000 : FiniteChecks.Interval terminalTest 3000 3008 :=
  FiniteChecks.interval_of_check terminalTest 3000 8 (by decide +kernel)

theorem terminal_data_03008 : FiniteChecks.Interval terminalTest 3008 3016 :=
  FiniteChecks.interval_of_check terminalTest 3008 8 (by decide +kernel)

theorem terminal_data_03016 : FiniteChecks.Interval terminalTest 3016 3024 :=
  FiniteChecks.interval_of_check terminalTest 3016 8 (by decide +kernel)

theorem terminal_data_03024 : FiniteChecks.Interval terminalTest 3024 3032 :=
  FiniteChecks.interval_of_check terminalTest 3024 8 (by decide +kernel)

theorem terminal_data_03032 : FiniteChecks.Interval terminalTest 3032 3040 :=
  FiniteChecks.interval_of_check terminalTest 3032 8 (by decide +kernel)

theorem terminal_data_03040 : FiniteChecks.Interval terminalTest 3040 3048 :=
  FiniteChecks.interval_of_check terminalTest 3040 8 (by decide +kernel)

theorem terminal_data_03048 : FiniteChecks.Interval terminalTest 3048 3056 :=
  FiniteChecks.interval_of_check terminalTest 3048 8 (by decide +kernel)

theorem terminal_data_03056 : FiniteChecks.Interval terminalTest 3056 3064 :=
  FiniteChecks.interval_of_check terminalTest 3056 8 (by decide +kernel)

theorem terminal_data_03064 : FiniteChecks.Interval terminalTest 3064 3072 :=
  FiniteChecks.interval_of_check terminalTest 3064 8 (by decide +kernel)

theorem terminal_data_03072 : FiniteChecks.Interval terminalTest 3072 3080 :=
  FiniteChecks.interval_of_check terminalTest 3072 8 (by decide +kernel)

theorem terminal_data_03080 : FiniteChecks.Interval terminalTest 3080 3088 :=
  FiniteChecks.interval_of_check terminalTest 3080 8 (by decide +kernel)

theorem terminal_data_03088 : FiniteChecks.Interval terminalTest 3088 3096 :=
  FiniteChecks.interval_of_check terminalTest 3088 8 (by decide +kernel)

theorem terminal_data_03096 : FiniteChecks.Interval terminalTest 3096 3104 :=
  FiniteChecks.interval_of_check terminalTest 3096 8 (by decide +kernel)

theorem terminal_data_03104 : FiniteChecks.Interval terminalTest 3104 3112 :=
  FiniteChecks.interval_of_check terminalTest 3104 8 (by decide +kernel)

theorem terminal_data_03112 : FiniteChecks.Interval terminalTest 3112 3120 :=
  FiniteChecks.interval_of_check terminalTest 3112 8 (by decide +kernel)

theorem terminal_data_03120 : FiniteChecks.Interval terminalTest 3120 3128 :=
  FiniteChecks.interval_of_check terminalTest 3120 8 (by decide +kernel)

theorem terminal_data_03128 : FiniteChecks.Interval terminalTest 3128 3136 :=
  FiniteChecks.interval_of_check terminalTest 3128 8 (by decide +kernel)

theorem terminal_data_03136 : FiniteChecks.Interval terminalTest 3136 3144 :=
  FiniteChecks.interval_of_check terminalTest 3136 8 (by decide +kernel)

theorem terminal_data_03144 : FiniteChecks.Interval terminalTest 3144 3152 :=
  FiniteChecks.interval_of_check terminalTest 3144 8 (by decide +kernel)

theorem terminal_data_03152 : FiniteChecks.Interval terminalTest 3152 3160 :=
  FiniteChecks.interval_of_check terminalTest 3152 8 (by decide +kernel)

theorem terminal_data_03160 : FiniteChecks.Interval terminalTest 3160 3168 :=
  FiniteChecks.interval_of_check terminalTest 3160 8 (by decide +kernel)

theorem terminal_data_03168 : FiniteChecks.Interval terminalTest 3168 3176 :=
  FiniteChecks.interval_of_check terminalTest 3168 8 (by decide +kernel)

theorem terminal_data_03176 : FiniteChecks.Interval terminalTest 3176 3184 :=
  FiniteChecks.interval_of_check terminalTest 3176 8 (by decide +kernel)

theorem terminal_data_03184 : FiniteChecks.Interval terminalTest 3184 3192 :=
  FiniteChecks.interval_of_check terminalTest 3184 8 (by decide +kernel)

theorem terminal_data_03192 : FiniteChecks.Interval terminalTest 3192 3200 :=
  FiniteChecks.interval_of_check terminalTest 3192 8 (by decide +kernel)

theorem terminal_data_03200 : FiniteChecks.Interval terminalTest 3200 3208 :=
  FiniteChecks.interval_of_check terminalTest 3200 8 (by decide +kernel)

theorem terminal_data_03208 : FiniteChecks.Interval terminalTest 3208 3216 :=
  FiniteChecks.interval_of_check terminalTest 3208 8 (by decide +kernel)

theorem terminal_data_03216 : FiniteChecks.Interval terminalTest 3216 3224 :=
  FiniteChecks.interval_of_check terminalTest 3216 8 (by decide +kernel)

theorem terminal_data_03224 : FiniteChecks.Interval terminalTest 3224 3232 :=
  FiniteChecks.interval_of_check terminalTest 3224 8 (by decide +kernel)

theorem terminal_data_03232 : FiniteChecks.Interval terminalTest 3232 3240 :=
  FiniteChecks.interval_of_check terminalTest 3232 8 (by decide +kernel)

theorem terminal_data_03240 : FiniteChecks.Interval terminalTest 3240 3248 :=
  FiniteChecks.interval_of_check terminalTest 3240 8 (by decide +kernel)

theorem terminal_data_03248 : FiniteChecks.Interval terminalTest 3248 3256 :=
  FiniteChecks.interval_of_check terminalTest 3248 8 (by decide +kernel)

theorem terminal_data_03256 : FiniteChecks.Interval terminalTest 3256 3264 :=
  FiniteChecks.interval_of_check terminalTest 3256 8 (by decide +kernel)

theorem terminal_data_03264 : FiniteChecks.Interval terminalTest 3264 3272 :=
  FiniteChecks.interval_of_check terminalTest 3264 8 (by decide +kernel)

theorem terminal_data_03272 : FiniteChecks.Interval terminalTest 3272 3280 :=
  FiniteChecks.interval_of_check terminalTest 3272 8 (by decide +kernel)

theorem terminal_data_03280 : FiniteChecks.Interval terminalTest 3280 3288 :=
  FiniteChecks.interval_of_check terminalTest 3280 8 (by decide +kernel)

theorem terminal_data_03288 : FiniteChecks.Interval terminalTest 3288 3296 :=
  FiniteChecks.interval_of_check terminalTest 3288 8 (by decide +kernel)

theorem terminal_data_03296 : FiniteChecks.Interval terminalTest 3296 3304 :=
  FiniteChecks.interval_of_check terminalTest 3296 8 (by decide +kernel)

theorem terminal_data_03304 : FiniteChecks.Interval terminalTest 3304 3312 :=
  FiniteChecks.interval_of_check terminalTest 3304 8 (by decide +kernel)

theorem terminal_data_03312 : FiniteChecks.Interval terminalTest 3312 3320 :=
  FiniteChecks.interval_of_check terminalTest 3312 8 (by decide +kernel)

theorem terminal_data_03320 : FiniteChecks.Interval terminalTest 3320 3328 :=
  FiniteChecks.interval_of_check terminalTest 3320 8 (by decide +kernel)

theorem terminal_data_03328 : FiniteChecks.Interval terminalTest 3328 3336 :=
  FiniteChecks.interval_of_check terminalTest 3328 8 (by decide +kernel)

theorem terminal_data_03336 : FiniteChecks.Interval terminalTest 3336 3344 :=
  FiniteChecks.interval_of_check terminalTest 3336 8 (by decide +kernel)

theorem terminal_data_03344 : FiniteChecks.Interval terminalTest 3344 3352 :=
  FiniteChecks.interval_of_check terminalTest 3344 8 (by decide +kernel)

theorem terminal_data_03352 : FiniteChecks.Interval terminalTest 3352 3360 :=
  FiniteChecks.interval_of_check terminalTest 3352 8 (by decide +kernel)

theorem terminal_data_03360 : FiniteChecks.Interval terminalTest 3360 3368 :=
  FiniteChecks.interval_of_check terminalTest 3360 8 (by decide +kernel)

theorem terminal_data_03368 : FiniteChecks.Interval terminalTest 3368 3376 :=
  FiniteChecks.interval_of_check terminalTest 3368 8 (by decide +kernel)

theorem terminal_data_03376 : FiniteChecks.Interval terminalTest 3376 3384 :=
  FiniteChecks.interval_of_check terminalTest 3376 8 (by decide +kernel)

theorem terminal_data_03384 : FiniteChecks.Interval terminalTest 3384 3392 :=
  FiniteChecks.interval_of_check terminalTest 3384 8 (by decide +kernel)

theorem terminal_data_03392 : FiniteChecks.Interval terminalTest 3392 3400 :=
  FiniteChecks.interval_of_check terminalTest 3392 8 (by decide +kernel)

theorem terminal_data_03400 : FiniteChecks.Interval terminalTest 3400 3408 :=
  FiniteChecks.interval_of_check terminalTest 3400 8 (by decide +kernel)

theorem terminal_data_03408 : FiniteChecks.Interval terminalTest 3408 3416 :=
  FiniteChecks.interval_of_check terminalTest 3408 8 (by decide +kernel)

theorem terminal_data_03416 : FiniteChecks.Interval terminalTest 3416 3424 :=
  FiniteChecks.interval_of_check terminalTest 3416 8 (by decide +kernel)

theorem terminal_data_03424 : FiniteChecks.Interval terminalTest 3424 3432 :=
  FiniteChecks.interval_of_check terminalTest 3424 8 (by decide +kernel)

theorem terminal_data_03432 : FiniteChecks.Interval terminalTest 3432 3440 :=
  FiniteChecks.interval_of_check terminalTest 3432 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
