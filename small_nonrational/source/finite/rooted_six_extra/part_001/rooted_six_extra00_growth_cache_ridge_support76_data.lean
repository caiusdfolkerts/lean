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
def ridgeSupport76_000 : List Nat := [15,65,69,70,71,358,361,363,366,368,370,373,375,378,380,382,385,387,390,392,1045,1047,1048,1051,1053,1057,1059,1060,1063,1065,1069,1071]
def ridgeSupport76_001 : List Nat := [1072,1075,1077,1117,1118,1120,1121,1122,1123,1125,1126,1128,1129,1131,1132,1138,1139,1141,1142,1143,1144,1146,1147,1149,1150,1152,1153,1159,1160,1162,1163,1164]
def ridgeSupport76_002 : List Nat := [1165,1167,1168,1170,1171,1173,1174,3640,3641,3642,3643,3644,3645,3646,3647,3652,3653,3658,3659,3664,3665,3666,3667,3668,3669,3670,3671,3676,3677,3682,3683,3688]
def ridgeSupport76_003 : List Nat := [3689,3690,3691,3692,3693,3712,3713,3714,3715,3716,3717,3736,3737,3738,3739,3740,3741,3760,3761,3762,3763,3764,3765,3784,3785,3786,3787,3788,3789,3808,3809,3810]
def ridgeSupport76_004 : List Nat := [3811,3812,3813,3832,3833,3834,3835,3836,3837,3841,3843,3847,3849,3853,3855,3898,3899,3910,3911,3919,3921,3925,3927,3934,3935,3946,3947,3970,3971,3982,3983,3991]
def ridgeSupport76_005 : List Nat := [3993,3997,3999,4006,4007,4018,4019,4042,4043,4054,4055,4063,4065,4069,4071,4078,4079,4090,4091,5944,5945,5956,5957,5980,5981,5992,5993,6007,6009,6013,6015,6016]
def ridgeSupport76_006 : List Nat := [6017,6028,6029,6052,6053,6064,6065,6079,6081,6085,6087,6088,6089,6100,6101,6124,6125,6136,6137,6151,6153,6157,6159,7276,7277,7278,7279,7280,7281,8056,8057,8058]
def ridgeSupport76_007 : List Nat := [8059,8060,8061,8080,8081,8082,8083,8084,8085,8092,8093,8094,8095,8096,8097,8104,8105,8110,8111,8122,8123,8128,8129,8140,8141,8146,8147,8569,8571,8575,8577,8587]
def ridgeSupport76_008 : List Nat := [8589,8593,8595,8605,8607,8611,8613]
def ridgeSupport76_code : Nat := 0x21a5868e19f8676193864618d862e18185fe17b85e5fd37f49fcd7f31fc17f01fbb7ee9faf7eb9fa97ea1fa17e81f9f7e79f9d7e71f957e51f937e49f917e41f7d7df1f7b7de9f797de1c7171c1c6f71b9c6d71b180f6035809601d7f95fe17ed5fb17d55f517c95f217c75f157c15efd7b15ec17a55e9178d5e317815e0177f5df57795ddd7695da175d5d717455d117395ce0ffb3fe8fef3fb8fe73f94fe13f7cfd73f58fcb3f28fb33ec8fa73e98f9f3e74f993e5cf8f3e38f833e08f6b3da8f5f3d78f573d54f513d3cf473d18f3b3ce8f0f3c34f093c1cf033c04efd3bf0efb3be8ef93be0ee53b90ee33b88ee13b80ecd3b30ecb3b28ec93b20eb53ad0eb33ac8eb13ac0e9d3a70e9b3a68e993a60e853a10e833a08e813a00e6d39b0e6b39a8e6939a0e633988e5d3970e573958e553950e533948e513940e4b3928e453910e3f38f8e3d38f0e3b38e8e3938e049612544931248490123c48d123048b1228488121c481120047e11f447b11e847811dc47611d447311c846c11ac46911a046611944631188461118045e117443510cc43010bc42d10a44271090423108441d106c418105c4150620186060c18105f817c05e817705d417205c016e05ac16905980470118045010400f
def ridgeSupport76_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport76_code
def ridgeSupport76_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport76_code
def ridgeSupport76_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport76_code
def ridgeSupport76_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport76_code
def ridgeSupport76_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport76_code
def ridgeSupport76_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport76_code
def ridgeSupport76_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport76_code
def ridgeSupport76_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport76_code
def ridgeSupport76_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport76_code
def ridgeSupport76_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport76_code
def ridgeSupport76_suffix_009 : List Nat := []
def ridgeSupport76_suffix_008 : List Nat := ridgeSupport76_008 ++ ridgeSupport76_suffix_009
def ridgeSupport76_suffix_007 : List Nat := ridgeSupport76_007 ++ ridgeSupport76_suffix_008
def ridgeSupport76_suffix_006 : List Nat := ridgeSupport76_006 ++ ridgeSupport76_suffix_007
def ridgeSupport76_suffix_005 : List Nat := ridgeSupport76_005 ++ ridgeSupport76_suffix_006
def ridgeSupport76_suffix_004 : List Nat := ridgeSupport76_004 ++ ridgeSupport76_suffix_005
def ridgeSupport76_suffix_003 : List Nat := ridgeSupport76_003 ++ ridgeSupport76_suffix_004
def ridgeSupport76_suffix_002 : List Nat := ridgeSupport76_002 ++ ridgeSupport76_suffix_003
def ridgeSupport76_suffix_001 : List Nat := ridgeSupport76_001 ++ ridgeSupport76_suffix_002
def ridgeSupport76_suffix_000 : List Nat := ridgeSupport76_000 ++ ridgeSupport76_suffix_001
theorem ridgeSupport76_source : candidateSupports 76 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport76_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
