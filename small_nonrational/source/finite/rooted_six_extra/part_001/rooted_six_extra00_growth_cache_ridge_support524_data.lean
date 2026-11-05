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
def ridgeSupport524_000 : List Nat := [18,68,71,73,74,383,384,386,391,393,407,408,410,415,417,419,420,422,427,429,1068,1070,1073,1074,1076,1092,1094,1097,1098,1100,1104,1106]
def ridgeSupport524_001 : List Nat := [1109,1110,1112,1137,1138,1140,1141,1144,1145,1146,1148,1149,1151,1156,1157,1158,1159,1161,1162,1165,1166,1167,1169,1170,1172,1177,1178,1179,1180,1182,1183,1186]
def ridgeSupport524_002 : List Nat := [1187,1188,1190,1191,1193,1198,1199,3644,3645,3650,3651,3656,3657,3658,3659,3660,3661,3662,3663,3668,3669,3674,3675,3680,3681,3682,3683,3684,3685,3686,3687,3706]
def ridgeSupport524_003 : List Nat := [3707,3708,3709,3710,3711,3730,3731,3732,3733,3734,3735,3754,3755,3756,3757,3758,3759,3778,3779,3780,3781,3782,3783,3802,3803,3804,3805,3806,3807,3826,3827,3828]
def ridgeSupport524_004 : List Nat := [3829,3830,3831,3832,3834,3838,3840,3844,3846,3850,3851,3852,3853,3854,3855,3974,3975,3986,3987,3988,3990,3994,3996,4010,4011,4022,4023,4046,4047,4058,4059,4060]
def ridgeSupport524_005 : List Nat := [4062,4066,4068,4082,4083,4094,4095,4118,4119,4130,4131,4132,4134,4138,4140,4154,4155,4166,4167,6020,6021,6032,6033,6056,6057,6068,6069,6076,6078,6082,6084,6092]
def ridgeSupport524_006 : List Nat := [6093,6104,6105,6128,6129,6140,6141,6148,6150,6154,6156,6164,6165,6176,6177,6200,6201,6212,6213,6220,6222,6226,6228,7294,7295,7296,7297,7298,7299,8074,8075,8076]
def ridgeSupport524_007 : List Nat := [8077,8078,8079,8080,8082,8086,8088,8090,8091,8092,8094,8098,8100,8102,8103,8126,8127,8132,8133,8144,8145,8150,8151,8162,8163,8168,8169,8584,8586,8590,8592,8602]
def ridgeSupport524_008 : List Nat := [8604,8608,8610,8620,8622,8626,8628]
def ridgeSupport524_code : Nat := 0x21b486ca1ae86b21a2868219c866a190863a18a8621fe97fa1fe37f89fd77f59fd17f41fc57f11fbf7ef9fa77e99fa47e89f9e7e71f9b7e69f987e59f927e41f8f7e39f8d7e31f8b7e29c837209c817201c7f71f9854614984e6131845611183960e18216081815605180c602980660117fd5ff17f15fc17d95f617cd5f317c45f097be5ef17b55ed17a95ea17915e417855e11047411903b40e902c40a9026409102340890174058fff3ff8ff33fc8fe43f88fde3f70fdb3f68fcf3f38fb73ed8fab3ea8f9c3e68f963e50f933e48f873e18f0f3c38f0d3c30f0b3c28f063c10f003bf8efa3be0ef73bd8ef53bd0ef33bc8edf3b78edd3b70edb3b68ec73b18ec53b10ec33b08eaf3ab8ead3ab0eab3aa8e973a58e953a50e933a48e7f39f8e7d39f0e7b39e8e673998e653990e633988e613980e5b3968e553950e4f3938e4d3930e4b3928e493920e433908e3d38f04af12b84a9129c4a612904a3128849f127849c126c49a12644941248491123c48e123448a12244871218485121047f11f447c11e847911e047511d047211c445811584551148450113044a1124446111043410c843110b842c06b41ab06981a4068c1a1067c19a06601970624187060818005fc04a01240470110012
def ridgeSupport524_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport524_code
def ridgeSupport524_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport524_code
def ridgeSupport524_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport524_code
def ridgeSupport524_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport524_code
def ridgeSupport524_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport524_code
def ridgeSupport524_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport524_code
def ridgeSupport524_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport524_code
def ridgeSupport524_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport524_code
def ridgeSupport524_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport524_code
def ridgeSupport524_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport524_code
def ridgeSupport524_suffix_009 : List Nat := []
def ridgeSupport524_suffix_008 : List Nat := ridgeSupport524_008 ++ ridgeSupport524_suffix_009
def ridgeSupport524_suffix_007 : List Nat := ridgeSupport524_007 ++ ridgeSupport524_suffix_008
def ridgeSupport524_suffix_006 : List Nat := ridgeSupport524_006 ++ ridgeSupport524_suffix_007
def ridgeSupport524_suffix_005 : List Nat := ridgeSupport524_005 ++ ridgeSupport524_suffix_006
def ridgeSupport524_suffix_004 : List Nat := ridgeSupport524_004 ++ ridgeSupport524_suffix_005
def ridgeSupport524_suffix_003 : List Nat := ridgeSupport524_003 ++ ridgeSupport524_suffix_004
def ridgeSupport524_suffix_002 : List Nat := ridgeSupport524_002 ++ ridgeSupport524_suffix_003
def ridgeSupport524_suffix_001 : List Nat := ridgeSupport524_001 ++ ridgeSupport524_suffix_002
def ridgeSupport524_suffix_000 : List Nat := ridgeSupport524_000 ++ ridgeSupport524_suffix_001
theorem ridgeSupport524_source : candidateSupports 524 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport524_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
