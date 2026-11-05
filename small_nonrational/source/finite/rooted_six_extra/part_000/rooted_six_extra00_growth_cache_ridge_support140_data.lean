module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport140_000 : List Nat := [16,66,69,72,73,359,360,362,367,369,394,397,399,402,404,406,409,411,414,416,1044,1046,1049,1050,1052,1081,1083,1084,1087,1089,1093,1095]
def ridgeSupport140_001 : List Nat := [1096,1099,1101,1116,1118,1119,1121,1122,1124,1126,1127,1129,1130,1133,1134,1137,1139,1140,1142,1143,1145,1147,1148,1150,1151,1154,1155,1180,1181,1183,1184,1185]
def ridgeSupport140_002 : List Nat := [1186,1188,1189,1191,1192,1194,1195,3640,3641,3646,3647,3648,3649,3650,3651,3654,3655,3660,3661,3664,3665,3670,3671,3672,3673,3674,3675,3678,3679,3684,3685,3694]
def ridgeSupport140_003 : List Nat := [3695,3696,3697,3698,3699,3718,3719,3720,3721,3722,3723,3742,3743,3744,3745,3746,3747,3766,3767,3768,3769,3770,3771,3790,3791,3792,3793,3794,3795,3814,3815,3816]
def ridgeSupport140_004 : List Nat := [3817,3818,3819,3835,3837,3838,3839,3840,3841,3842,3843,3845,3848,3851,3854,3900,3901,3912,3913,3917,3920,3923,3926,3936,3937,3948,3949,3972,3973,3984,3985,3989]
def ridgeSupport140_005 : List Nat := [3992,3995,3998,4008,4009,4020,4021,4114,4115,4126,4127,4135,4137,4141,4143,4150,4151,4162,4163,5946,5947,5958,5959,5982,5983,5994,5995,6005,6008,6011,6014,6018]
def ridgeSupport140_006 : List Nat := [6019,6030,6031,6054,6055,6066,6067,6077,6080,6083,6086,6160,6161,6172,6173,6196,6197,6208,6209,6223,6225,6229,6231,7282,7283,7284,7285,7286,7287,8062,8063,8064]
def ridgeSupport140_007 : List Nat := [8065,8066,8067,8083,8085,8086,8087,8088,8089,8095,8097,8098,8099,8100,8101,8106,8107,8112,8113,8124,8125,8130,8131,8158,8159,8164,8165,8567,8570,8573,8576,8585]
def ridgeSupport140_008 : List Nat := [8588,8591,8594,8623,8625,8629,8631]
def ridgeSupport140_code : Nat := 0x21b786d61b186be192863e18c862618085f617a85ddfe57f91fdf7f79fc37f09fbd7ef1fb17ec1fab7ea9fa57e91fa37e89fa17e7df997e61f977e59f957e4df837e09f817e01f7f7df9c7771d9c7571d1c7371c98576155851613d841610183560d181d607181160417c65f0d7c05ef57b35ec97a75e9978f5e397835e0977e5ded7785dd576b5da975f5d797475d1973b5ce9043410903740d902f40b5029409d01f40790134048fb53ed0fa93ea0f9e3e6cf983e54f913e40f853e10f6d3db0f613d80f563d4cf503d34f493d20f3d3cf0f0e3c2cf083c14f033c08f013c00eff3bf8efd3beceeb3ba8ee93ba0ee73b98ed33b48ed13b40ecf3b38ebb3ae8eb93ae0eb73ad8ea33a88ea13a80e9f3a78e8b3a28e893a20e873a18e7339c8e7139c0e6f39b8e653990e5f3978e5b3968e593960e573958e513940e4d3930e473918e433908e413900e3f38f8e3938e04ab12a84a8129c4a512904a212844a0127c49d1270483120847f11f847c11ec47911dc47611d047311c446e11b446a11a446711984641188461117c45e117044d112c448111c445110443f10f043b10e441c10684191058414068019e066c1990658194064818f063418a05c416f05a8168059c04901200450108010
def ridgeSupport140_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport140_code
def ridgeSupport140_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport140_code
def ridgeSupport140_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport140_code
def ridgeSupport140_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport140_code
def ridgeSupport140_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport140_code
def ridgeSupport140_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport140_code
def ridgeSupport140_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport140_code
def ridgeSupport140_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport140_code
def ridgeSupport140_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport140_code
def ridgeSupport140_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport140_code
def ridgeSupport140_suffix_009 : List Nat := []
def ridgeSupport140_suffix_008 : List Nat := ridgeSupport140_008 ++ ridgeSupport140_suffix_009
def ridgeSupport140_suffix_007 : List Nat := ridgeSupport140_007 ++ ridgeSupport140_suffix_008
def ridgeSupport140_suffix_006 : List Nat := ridgeSupport140_006 ++ ridgeSupport140_suffix_007
def ridgeSupport140_suffix_005 : List Nat := ridgeSupport140_005 ++ ridgeSupport140_suffix_006
def ridgeSupport140_suffix_004 : List Nat := ridgeSupport140_004 ++ ridgeSupport140_suffix_005
def ridgeSupport140_suffix_003 : List Nat := ridgeSupport140_003 ++ ridgeSupport140_suffix_004
def ridgeSupport140_suffix_002 : List Nat := ridgeSupport140_002 ++ ridgeSupport140_suffix_003
def ridgeSupport140_suffix_001 : List Nat := ridgeSupport140_001 ++ ridgeSupport140_suffix_002
def ridgeSupport140_suffix_000 : List Nat := ridgeSupport140_000 ++ ridgeSupport140_suffix_001
theorem ridgeSupport140_source : candidateSupports 140 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport140_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
