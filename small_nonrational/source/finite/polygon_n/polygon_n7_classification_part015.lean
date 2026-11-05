module

public import PolygonN7ClassificationPart014

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_02752_02768 : FiniteChecks.Interval terminalTest 2752 2768 :=
  FiniteChecks.interval_append terminalTest 2752 2760 2768 terminal_data_02752 terminal_data_02760

theorem terminal_data_join_02768_02784 : FiniteChecks.Interval terminalTest 2768 2784 :=
  FiniteChecks.interval_append terminalTest 2768 2776 2784 terminal_data_02768 terminal_data_02776

theorem terminal_data_join_02752_02784 : FiniteChecks.Interval terminalTest 2752 2784 :=
  FiniteChecks.interval_append terminalTest 2752 2768 2784 terminal_data_join_02752_02768 terminal_data_join_02768_02784

theorem terminal_data_join_02728_02784 : FiniteChecks.Interval terminalTest 2728 2784 :=
  FiniteChecks.interval_append terminalTest 2728 2752 2784 terminal_data_join_02728_02752 terminal_data_join_02752_02784

theorem terminal_data_join_02784_02800 : FiniteChecks.Interval terminalTest 2784 2800 :=
  FiniteChecks.interval_append terminalTest 2784 2792 2800 terminal_data_02784 terminal_data_02792

theorem terminal_data_join_02800_02816 : FiniteChecks.Interval terminalTest 2800 2816 :=
  FiniteChecks.interval_append terminalTest 2800 2808 2816 terminal_data_02800 terminal_data_02808

theorem terminal_data_join_02784_02816 : FiniteChecks.Interval terminalTest 2784 2816 :=
  FiniteChecks.interval_append terminalTest 2784 2800 2816 terminal_data_join_02784_02800 terminal_data_join_02800_02816

theorem terminal_data_join_02816_02832 : FiniteChecks.Interval terminalTest 2816 2832 :=
  FiniteChecks.interval_append terminalTest 2816 2824 2832 terminal_data_02816 terminal_data_02824

theorem terminal_data_join_02832_02848 : FiniteChecks.Interval terminalTest 2832 2848 :=
  FiniteChecks.interval_append terminalTest 2832 2840 2848 terminal_data_02832 terminal_data_02840

theorem terminal_data_join_02816_02848 : FiniteChecks.Interval terminalTest 2816 2848 :=
  FiniteChecks.interval_append terminalTest 2816 2832 2848 terminal_data_join_02816_02832 terminal_data_join_02832_02848

theorem terminal_data_join_02784_02848 : FiniteChecks.Interval terminalTest 2784 2848 :=
  FiniteChecks.interval_append terminalTest 2784 2816 2848 terminal_data_join_02784_02816 terminal_data_join_02816_02848

theorem terminal_data_join_02728_02848 : FiniteChecks.Interval terminalTest 2728 2848 :=
  FiniteChecks.interval_append terminalTest 2728 2784 2848 terminal_data_join_02728_02784 terminal_data_join_02784_02848

theorem terminal_data_join_02608_02848 : FiniteChecks.Interval terminalTest 2608 2848 :=
  FiniteChecks.interval_append terminalTest 2608 2728 2848 terminal_data_join_02608_02728 terminal_data_join_02728_02848

theorem terminal_data_join_02368_02848 : FiniteChecks.Interval terminalTest 2368 2848 :=
  FiniteChecks.interval_append terminalTest 2368 2608 2848 terminal_data_join_02368_02608 terminal_data_join_02608_02848

theorem terminal_data_join_01896_02848 : FiniteChecks.Interval terminalTest 1896 2848 :=
  FiniteChecks.interval_append terminalTest 1896 2368 2848 terminal_data_join_01896_02368 terminal_data_join_02368_02848

theorem terminal_data_join_02856_02872 : FiniteChecks.Interval terminalTest 2856 2872 :=
  FiniteChecks.interval_append terminalTest 2856 2864 2872 terminal_data_02856 terminal_data_02864

theorem terminal_data_join_02848_02872 : FiniteChecks.Interval terminalTest 2848 2872 :=
  FiniteChecks.interval_append terminalTest 2848 2856 2872 terminal_data_02848 terminal_data_join_02856_02872

theorem terminal_data_join_02872_02888 : FiniteChecks.Interval terminalTest 2872 2888 :=
  FiniteChecks.interval_append terminalTest 2872 2880 2888 terminal_data_02872 terminal_data_02880

theorem terminal_data_join_02888_02904 : FiniteChecks.Interval terminalTest 2888 2904 :=
  FiniteChecks.interval_append terminalTest 2888 2896 2904 terminal_data_02888 terminal_data_02896

theorem terminal_data_join_02872_02904 : FiniteChecks.Interval terminalTest 2872 2904 :=
  FiniteChecks.interval_append terminalTest 2872 2888 2904 terminal_data_join_02872_02888 terminal_data_join_02888_02904

theorem terminal_data_join_02848_02904 : FiniteChecks.Interval terminalTest 2848 2904 :=
  FiniteChecks.interval_append terminalTest 2848 2872 2904 terminal_data_join_02848_02872 terminal_data_join_02872_02904

theorem terminal_data_join_02912_02928 : FiniteChecks.Interval terminalTest 2912 2928 :=
  FiniteChecks.interval_append terminalTest 2912 2920 2928 terminal_data_02912 terminal_data_02920

theorem terminal_data_join_02904_02928 : FiniteChecks.Interval terminalTest 2904 2928 :=
  FiniteChecks.interval_append terminalTest 2904 2912 2928 terminal_data_02904 terminal_data_join_02912_02928

theorem terminal_data_join_02928_02944 : FiniteChecks.Interval terminalTest 2928 2944 :=
  FiniteChecks.interval_append terminalTest 2928 2936 2944 terminal_data_02928 terminal_data_02936

theorem terminal_data_join_02944_02960 : FiniteChecks.Interval terminalTest 2944 2960 :=
  FiniteChecks.interval_append terminalTest 2944 2952 2960 terminal_data_02944 terminal_data_02952

theorem terminal_data_join_02928_02960 : FiniteChecks.Interval terminalTest 2928 2960 :=
  FiniteChecks.interval_append terminalTest 2928 2944 2960 terminal_data_join_02928_02944 terminal_data_join_02944_02960

theorem terminal_data_join_02904_02960 : FiniteChecks.Interval terminalTest 2904 2960 :=
  FiniteChecks.interval_append terminalTest 2904 2928 2960 terminal_data_join_02904_02928 terminal_data_join_02928_02960

theorem terminal_data_join_02848_02960 : FiniteChecks.Interval terminalTest 2848 2960 :=
  FiniteChecks.interval_append terminalTest 2848 2904 2960 terminal_data_join_02848_02904 terminal_data_join_02904_02960

theorem terminal_data_join_02968_02984 : FiniteChecks.Interval terminalTest 2968 2984 :=
  FiniteChecks.interval_append terminalTest 2968 2976 2984 terminal_data_02968 terminal_data_02976

theorem terminal_data_join_02960_02984 : FiniteChecks.Interval terminalTest 2960 2984 :=
  FiniteChecks.interval_append terminalTest 2960 2968 2984 terminal_data_02960 terminal_data_join_02968_02984

theorem terminal_data_join_02984_03000 : FiniteChecks.Interval terminalTest 2984 3000 :=
  FiniteChecks.interval_append terminalTest 2984 2992 3000 terminal_data_02984 terminal_data_02992

theorem terminal_data_join_03000_03016 : FiniteChecks.Interval terminalTest 3000 3016 :=
  FiniteChecks.interval_append terminalTest 3000 3008 3016 terminal_data_03000 terminal_data_03008

theorem terminal_data_join_02984_03016 : FiniteChecks.Interval terminalTest 2984 3016 :=
  FiniteChecks.interval_append terminalTest 2984 3000 3016 terminal_data_join_02984_03000 terminal_data_join_03000_03016

theorem terminal_data_join_02960_03016 : FiniteChecks.Interval terminalTest 2960 3016 :=
  FiniteChecks.interval_append terminalTest 2960 2984 3016 terminal_data_join_02960_02984 terminal_data_join_02984_03016

theorem terminal_data_join_03016_03032 : FiniteChecks.Interval terminalTest 3016 3032 :=
  FiniteChecks.interval_append terminalTest 3016 3024 3032 terminal_data_03016 terminal_data_03024

theorem terminal_data_join_03032_03048 : FiniteChecks.Interval terminalTest 3032 3048 :=
  FiniteChecks.interval_append terminalTest 3032 3040 3048 terminal_data_03032 terminal_data_03040

theorem terminal_data_join_03016_03048 : FiniteChecks.Interval terminalTest 3016 3048 :=
  FiniteChecks.interval_append terminalTest 3016 3032 3048 terminal_data_join_03016_03032 terminal_data_join_03032_03048

theorem terminal_data_join_03048_03064 : FiniteChecks.Interval terminalTest 3048 3064 :=
  FiniteChecks.interval_append terminalTest 3048 3056 3064 terminal_data_03048 terminal_data_03056

theorem terminal_data_join_03064_03080 : FiniteChecks.Interval terminalTest 3064 3080 :=
  FiniteChecks.interval_append terminalTest 3064 3072 3080 terminal_data_03064 terminal_data_03072

theorem terminal_data_join_03048_03080 : FiniteChecks.Interval terminalTest 3048 3080 :=
  FiniteChecks.interval_append terminalTest 3048 3064 3080 terminal_data_join_03048_03064 terminal_data_join_03064_03080

theorem terminal_data_join_03016_03080 : FiniteChecks.Interval terminalTest 3016 3080 :=
  FiniteChecks.interval_append terminalTest 3016 3048 3080 terminal_data_join_03016_03048 terminal_data_join_03048_03080

theorem terminal_data_join_02960_03080 : FiniteChecks.Interval terminalTest 2960 3080 :=
  FiniteChecks.interval_append terminalTest 2960 3016 3080 terminal_data_join_02960_03016 terminal_data_join_03016_03080

theorem terminal_data_join_02848_03080 : FiniteChecks.Interval terminalTest 2848 3080 :=
  FiniteChecks.interval_append terminalTest 2848 2960 3080 terminal_data_join_02848_02960 terminal_data_join_02960_03080

theorem terminal_data_join_03088_03104 : FiniteChecks.Interval terminalTest 3088 3104 :=
  FiniteChecks.interval_append terminalTest 3088 3096 3104 terminal_data_03088 terminal_data_03096

theorem terminal_data_join_03080_03104 : FiniteChecks.Interval terminalTest 3080 3104 :=
  FiniteChecks.interval_append terminalTest 3080 3088 3104 terminal_data_03080 terminal_data_join_03088_03104

theorem terminal_data_join_03104_03120 : FiniteChecks.Interval terminalTest 3104 3120 :=
  FiniteChecks.interval_append terminalTest 3104 3112 3120 terminal_data_03104 terminal_data_03112

theorem terminal_data_join_03120_03136 : FiniteChecks.Interval terminalTest 3120 3136 :=
  FiniteChecks.interval_append terminalTest 3120 3128 3136 terminal_data_03120 terminal_data_03128

theorem terminal_data_join_03104_03136 : FiniteChecks.Interval terminalTest 3104 3136 :=
  FiniteChecks.interval_append terminalTest 3104 3120 3136 terminal_data_join_03104_03120 terminal_data_join_03120_03136

theorem terminal_data_join_03080_03136 : FiniteChecks.Interval terminalTest 3080 3136 :=
  FiniteChecks.interval_append terminalTest 3080 3104 3136 terminal_data_join_03080_03104 terminal_data_join_03104_03136

theorem terminal_data_join_03136_03152 : FiniteChecks.Interval terminalTest 3136 3152 :=
  FiniteChecks.interval_append terminalTest 3136 3144 3152 terminal_data_03136 terminal_data_03144

theorem terminal_data_join_03152_03168 : FiniteChecks.Interval terminalTest 3152 3168 :=
  FiniteChecks.interval_append terminalTest 3152 3160 3168 terminal_data_03152 terminal_data_03160

theorem terminal_data_join_03136_03168 : FiniteChecks.Interval terminalTest 3136 3168 :=
  FiniteChecks.interval_append terminalTest 3136 3152 3168 terminal_data_join_03136_03152 terminal_data_join_03152_03168

theorem terminal_data_join_03168_03184 : FiniteChecks.Interval terminalTest 3168 3184 :=
  FiniteChecks.interval_append terminalTest 3168 3176 3184 terminal_data_03168 terminal_data_03176

theorem terminal_data_join_03184_03200 : FiniteChecks.Interval terminalTest 3184 3200 :=
  FiniteChecks.interval_append terminalTest 3184 3192 3200 terminal_data_03184 terminal_data_03192

theorem terminal_data_join_03168_03200 : FiniteChecks.Interval terminalTest 3168 3200 :=
  FiniteChecks.interval_append terminalTest 3168 3184 3200 terminal_data_join_03168_03184 terminal_data_join_03184_03200

theorem terminal_data_join_03136_03200 : FiniteChecks.Interval terminalTest 3136 3200 :=
  FiniteChecks.interval_append terminalTest 3136 3168 3200 terminal_data_join_03136_03168 terminal_data_join_03168_03200

theorem terminal_data_join_03080_03200 : FiniteChecks.Interval terminalTest 3080 3200 :=
  FiniteChecks.interval_append terminalTest 3080 3136 3200 terminal_data_join_03080_03136 terminal_data_join_03136_03200

theorem terminal_data_join_03208_03224 : FiniteChecks.Interval terminalTest 3208 3224 :=
  FiniteChecks.interval_append terminalTest 3208 3216 3224 terminal_data_03208 terminal_data_03216

theorem terminal_data_join_03200_03224 : FiniteChecks.Interval terminalTest 3200 3224 :=
  FiniteChecks.interval_append terminalTest 3200 3208 3224 terminal_data_03200 terminal_data_join_03208_03224

theorem terminal_data_join_03224_03240 : FiniteChecks.Interval terminalTest 3224 3240 :=
  FiniteChecks.interval_append terminalTest 3224 3232 3240 terminal_data_03224 terminal_data_03232

theorem terminal_data_join_03240_03256 : FiniteChecks.Interval terminalTest 3240 3256 :=
  FiniteChecks.interval_append terminalTest 3240 3248 3256 terminal_data_03240 terminal_data_03248

theorem terminal_data_join_03224_03256 : FiniteChecks.Interval terminalTest 3224 3256 :=
  FiniteChecks.interval_append terminalTest 3224 3240 3256 terminal_data_join_03224_03240 terminal_data_join_03240_03256

theorem terminal_data_join_03200_03256 : FiniteChecks.Interval terminalTest 3200 3256 :=
  FiniteChecks.interval_append terminalTest 3200 3224 3256 terminal_data_join_03200_03224 terminal_data_join_03224_03256

theorem terminal_data_join_03256_03272 : FiniteChecks.Interval terminalTest 3256 3272 :=
  FiniteChecks.interval_append terminalTest 3256 3264 3272 terminal_data_03256 terminal_data_03264


end Papers.RationalityTen.ConcretePolygonClassification.N7
