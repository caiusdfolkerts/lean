module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart014

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join_2 02752 02768 2752 2768 2760 02760
cert_terminal_data_join_2 02768 02784 2768 2784 2776 02776
cert_terminal_data_join 02752 02784 2752 2784 2768 02768
cert_terminal_data_join 02728 02784 2728 2784 2752 02752
cert_terminal_data_join_2 02784 02800 2784 2800 2792 02792
cert_terminal_data_join_2 02800 02816 2800 2816 2808 02808
cert_terminal_data_join 02784 02816 2784 2816 2800 02800
cert_terminal_data_join_2 02816 02832 2816 2832 2824 02824
cert_terminal_data_join_2 02832 02848 2832 2848 2840 02840
cert_terminal_data_join 02816 02848 2816 2848 2832 02832
cert_terminal_data_join 02784 02848 2784 2848 2816 02816
cert_terminal_data_join 02728 02848 2728 2848 2784 02784
cert_terminal_data_join 02608 02848 2608 2848 2728 02728
cert_terminal_data_join 02368 02848 2368 2848 2608 02608
cert_terminal_data_join 01896 02848 1896 2848 2368 02368
cert_terminal_data_join_2 02856 02872 2856 2872 2864 02864
cert_terminal_data_join_3 02848 02872 2848 2872 2856 02856
cert_terminal_data_join_2 02872 02888 2872 2888 2880 02880
cert_terminal_data_join_2 02888 02904 2888 2904 2896 02896
cert_terminal_data_join 02872 02904 2872 2904 2888 02888
cert_terminal_data_join 02848 02904 2848 2904 2872 02872
cert_terminal_data_join_2 02912 02928 2912 2928 2920 02920
cert_terminal_data_join_3 02904 02928 2904 2928 2912 02912
cert_terminal_data_join_2 02928 02944 2928 2944 2936 02936
cert_terminal_data_join_2 02944 02960 2944 2960 2952 02952
cert_terminal_data_join 02928 02960 2928 2960 2944 02944
cert_terminal_data_join 02904 02960 2904 2960 2928 02928
cert_terminal_data_join 02848 02960 2848 2960 2904 02904
cert_terminal_data_join_2 02968 02984 2968 2984 2976 02976
cert_terminal_data_join_3 02960 02984 2960 2984 2968 02968
cert_terminal_data_join_2 02984 03000 2984 3000 2992 02992
cert_terminal_data_join_2 03000 03016 3000 3016 3008 03008
cert_terminal_data_join 02984 03016 2984 3016 3000 03000
cert_terminal_data_join 02960 03016 2960 3016 2984 02984
cert_terminal_data_join_2 03016 03032 3016 3032 3024 03024
cert_terminal_data_join_2 03032 03048 3032 3048 3040 03040
cert_terminal_data_join 03016 03048 3016 3048 3032 03032
cert_terminal_data_join_2 03048 03064 3048 3064 3056 03056
cert_terminal_data_join_2 03064 03080 3064 3080 3072 03072
cert_terminal_data_join 03048 03080 3048 3080 3064 03064
cert_terminal_data_join 03016 03080 3016 3080 3048 03048
cert_terminal_data_join 02960 03080 2960 3080 3016 03016
cert_terminal_data_join 02848 03080 2848 3080 2960 02960
cert_terminal_data_join_2 03088 03104 3088 3104 3096 03096
cert_terminal_data_join_3 03080 03104 3080 3104 3088 03088
cert_terminal_data_join_2 03104 03120 3104 3120 3112 03112
cert_terminal_data_join_2 03120 03136 3120 3136 3128 03128
cert_terminal_data_join 03104 03136 3104 3136 3120 03120
cert_terminal_data_join 03080 03136 3080 3136 3104 03104
cert_terminal_data_join_2 03136 03152 3136 3152 3144 03144
cert_terminal_data_join_2 03152 03168 3152 3168 3160 03160
cert_terminal_data_join 03136 03168 3136 3168 3152 03152
cert_terminal_data_join_2 03168 03184 3168 3184 3176 03176
cert_terminal_data_join_2 03184 03200 3184 3200 3192 03192
cert_terminal_data_join 03168 03200 3168 3200 3184 03184
cert_terminal_data_join 03136 03200 3136 3200 3168 03168
cert_terminal_data_join 03080 03200 3080 3200 3136 03136
cert_terminal_data_join_2 03208 03224 3208 3224 3216 03216
cert_terminal_data_join_3 03200 03224 3200 3224 3208 03208
cert_terminal_data_join_2 03224 03240 3224 3240 3232 03232
cert_terminal_data_join_2 03240 03256 3240 3256 3248 03248
cert_terminal_data_join 03224 03256 3224 3256 3240 03240
cert_terminal_data_join 03200 03256 3200 3256 3224 03224
theorem terminal_data_join_03256_03272 : FiniteChecks.Interval terminalTest 3256 3272 :=
  FiniteChecks.interval_append terminalTest 3256 3264 3272 terminal_data_03256 terminal_data_03264


end Papers.RationalityTen.ConcretePolygonClassification.N7
