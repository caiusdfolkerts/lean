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
def ridgeSupport268_000 : List Nat := [17,67,70,72,74,371,372,374,379,381,395,396,398,403,405,418,421,423,426,428,1056,1058,1061,1062,1064,1080,1082,1085,1086,1088,1105,1107]
def ridgeSupport268_001 : List Nat := [1108,1111,1113,1116,1117,1119,1120,1123,1124,1125,1127,1128,1130,1135,1136,1158,1160,1161,1163,1164,1166,1168,1169,1171,1172,1175,1176,1179,1181,1182,1184,1185]
def ridgeSupport268_002 : List Nat := [1187,1189,1190,1192,1193,1196,1197,3642,3643,3648,3649,3652,3653,3654,3655,3656,3657,3662,3663,3666,3667,3672,3673,3676,3677,3678,3679,3680,3681,3686,3687,3700]
def ridgeSupport268_003 : List Nat := [3701,3702,3703,3704,3705,3724,3725,3726,3727,3728,3729,3748,3749,3750,3751,3752,3753,3772,3773,3774,3775,3776,3777,3796,3797,3798,3799,3800,3801,3820,3821,3822]
def ridgeSupport268_004 : List Nat := [3823,3824,3825,3833,3836,3839,3842,3844,3845,3846,3847,3848,3849,3850,3852,3902,3903,3914,3915,3916,3918,3922,3924,3938,3939,3950,3951,4044,4045,4056,4057,4061]
def ridgeSupport268_005 : List Nat := [4064,4067,4070,4080,4081,4092,4093,4116,4117,4128,4129,4133,4136,4139,4142,4152,4153,4164,4165,5948,5949,5960,5961,5984,5985,5996,5997,6004,6006,6010,6012,6090]
def ridgeSupport268_006 : List Nat := [6091,6102,6103,6126,6127,6138,6139,6149,6152,6155,6158,6162,6163,6174,6175,6198,6199,6210,6211,6221,6224,6227,6230,7288,7289,7290,7291,7292,7293,8068,8069,8070]
def ridgeSupport268_007 : List Nat := [8071,8072,8073,8081,8084,8087,8089,8090,8091,8093,8096,8099,8101,8102,8103,8108,8109,8114,8115,8142,8143,8148,8149,8160,8161,8166,8167,8566,8568,8572,8574,8603]
def ridgeSupport268_008 : List Nat := [8606,8609,8612,8621,8624,8627,8630]
def ridgeSupport268_code : Nat := 0x21b686ce1b086b61a4868619e866e17e85f217885d9fe77f99fe17f81fd57f51fcf7f39fb37ec9fad7eb1fa77e99fa57e8dfa07e75f9b7e69f997e5df947e45f897e21f877e19f857e11c7d71f1c7b71e9c7971e1856614d8506135843610983760d981f6079813604980e602d80860157fb5fe97ef5fb97d75f597cb5f2977c5de97765dd176d5db17615d817495d2173d5cf1045411103940e102e40ad028409502140810154050ffd3ff0ff13fc0fe63f8cfe03f74fd93f60fcd3f30f6f3db8f633d88f543d48f4e3d30f4b3d28f3f3cf8f0c3c28f093c20f073c18f053c10f023bfcefc3be4ef13bc0eef3bb8eed3bb0ed93b60ed73b58ed53b50ec13b00ebf3af8ebd3af0ea93aa0ea73a98ea53a90e913a40e8f3a38e8d3a30e7939e0e7739d8e7539d0e673998e613980e5f3978e5d3970e593960e533948e4f3938e493920e473918e453910e413900e3b38e84ad12b04a912a04a612944a312844a0127849d126c498125c494124c491124048e123048b1224488121847011bc46a11a04671194464118c460117c45d1170459115c454114c451110043e10f443a10e04281098425108842006b01aa069c1a50688195064c18e063018b05f417b05d817405cc04a0120046010c011
def ridgeSupport268_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport268_code
def ridgeSupport268_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport268_code
def ridgeSupport268_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport268_code
def ridgeSupport268_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport268_code
def ridgeSupport268_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport268_code
def ridgeSupport268_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport268_code
def ridgeSupport268_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport268_code
def ridgeSupport268_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport268_code
def ridgeSupport268_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport268_code
def ridgeSupport268_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport268_code
def ridgeSupport268_suffix_009 : List Nat := []
def ridgeSupport268_suffix_008 : List Nat := ridgeSupport268_008 ++ ridgeSupport268_suffix_009
def ridgeSupport268_suffix_007 : List Nat := ridgeSupport268_007 ++ ridgeSupport268_suffix_008
def ridgeSupport268_suffix_006 : List Nat := ridgeSupport268_006 ++ ridgeSupport268_suffix_007
def ridgeSupport268_suffix_005 : List Nat := ridgeSupport268_005 ++ ridgeSupport268_suffix_006
def ridgeSupport268_suffix_004 : List Nat := ridgeSupport268_004 ++ ridgeSupport268_suffix_005
def ridgeSupport268_suffix_003 : List Nat := ridgeSupport268_003 ++ ridgeSupport268_suffix_004
def ridgeSupport268_suffix_002 : List Nat := ridgeSupport268_002 ++ ridgeSupport268_suffix_003
def ridgeSupport268_suffix_001 : List Nat := ridgeSupport268_001 ++ ridgeSupport268_suffix_002
def ridgeSupport268_suffix_000 : List Nat := ridgeSupport268_000 ++ ridgeSupport268_suffix_001
theorem ridgeSupport268_source : candidateSupports 268 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport268_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
