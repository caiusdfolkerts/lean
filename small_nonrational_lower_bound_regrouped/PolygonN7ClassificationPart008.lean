module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart007

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data 02928 2928 2936 8
cert_terminal_data 02936 2936 2944 8
cert_terminal_data 02944 2944 2952 8
cert_terminal_data 02952 2952 2960 8
cert_terminal_data 02960 2960 2968 8
cert_terminal_data 02968 2968 2976 8
cert_terminal_data 02976 2976 2984 8
cert_terminal_data 02984 2984 2992 8
cert_terminal_data 02992 2992 3000 8
cert_terminal_data 03000 3000 3008 8
cert_terminal_data 03008 3008 3016 8
cert_terminal_data 03016 3016 3024 8
cert_terminal_data 03024 3024 3032 8
cert_terminal_data 03032 3032 3040 8
cert_terminal_data 03040 3040 3048 8
cert_terminal_data 03048 3048 3056 8
cert_terminal_data 03056 3056 3064 8
cert_terminal_data 03064 3064 3072 8
cert_terminal_data 03072 3072 3080 8
cert_terminal_data 03080 3080 3088 8
cert_terminal_data 03088 3088 3096 8
cert_terminal_data 03096 3096 3104 8
cert_terminal_data 03104 3104 3112 8
cert_terminal_data 03112 3112 3120 8
cert_terminal_data 03120 3120 3128 8
cert_terminal_data 03128 3128 3136 8
cert_terminal_data 03136 3136 3144 8
cert_terminal_data 03144 3144 3152 8
cert_terminal_data 03152 3152 3160 8
cert_terminal_data 03160 3160 3168 8
cert_terminal_data 03168 3168 3176 8
cert_terminal_data 03176 3176 3184 8
cert_terminal_data 03184 3184 3192 8
cert_terminal_data 03192 3192 3200 8
cert_terminal_data 03200 3200 3208 8
cert_terminal_data 03208 3208 3216 8
cert_terminal_data 03216 3216 3224 8
cert_terminal_data 03224 3224 3232 8
cert_terminal_data 03232 3232 3240 8
cert_terminal_data 03240 3240 3248 8
cert_terminal_data 03248 3248 3256 8
cert_terminal_data 03256 3256 3264 8
cert_terminal_data 03264 3264 3272 8
cert_terminal_data 03272 3272 3280 8
cert_terminal_data 03280 3280 3288 8
cert_terminal_data 03288 3288 3296 8
cert_terminal_data 03296 3296 3304 8
cert_terminal_data 03304 3304 3312 8
cert_terminal_data 03312 3312 3320 8
cert_terminal_data 03320 3320 3328 8
cert_terminal_data 03328 3328 3336 8
cert_terminal_data 03336 3336 3344 8
cert_terminal_data 03344 3344 3352 8
cert_terminal_data 03352 3352 3360 8
cert_terminal_data 03360 3360 3368 8
cert_terminal_data 03368 3368 3376 8
cert_terminal_data 03376 3376 3384 8
cert_terminal_data 03384 3384 3392 8
cert_terminal_data 03392 3392 3400 8
cert_terminal_data 03400 3400 3408 8
cert_terminal_data 03408 3408 3416 8
cert_terminal_data 03416 3416 3424 8
cert_terminal_data 03424 3424 3432 8
theorem terminal_data_03432 : FiniteChecks.Interval terminalTest 3432 3440 :=
  FiniteChecks.interval_of_check terminalTest 3432 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
