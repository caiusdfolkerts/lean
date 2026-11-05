module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport800_000 : List Nat := [52,82,92,99,100,675,676,677,678,685,686,814,815,816,819,820,825,826,831,833,835,836,837,840,841,846,847,852,854,1049,1050,1051]
def ridgeSupport800_001 : List Nat := [1052,1059,1060,1188,1189,1190,1193,1194,1199,1200,1205,1207,1209,1210,1211,1214,1215,1220,1221,1226,1228,1297,1298,1299,1302,1303,1308,1309,1314,1316,1318,1319]
def ridgeSupport800_002 : List Nat := [1320,1323,1324,1329,1330,1335,1337,1363,1364,1368,1369,1370,1371,1373,1374,1382,1384,1385,1387,3742,3744,3748,3750,3828,3829,3834,3835,3836,3837,3842,3843,3848]
def ridgeSupport800_003 : List Nat := [3850,3854,3856,3876,3877,3882,3883,3910,3912,3916,3918,3924,3925,3930,3931,3932,3933,3938,3939,3956,3957,3962,3963,3982,3984,3988,3990,4068,4069,4074,4075,4076]
def ridgeSupport800_004 : List Nat := [4077,4082,4083,4088,4090,4094,4096,4116,4117,4122,4123,4150,4152,4156,4158,4164,4165,4170,4171,4172,4173,4178,4179,4196,4197,4202,4203,4372,4374,4384,4386,4400]
def ridgeSupport800_005 : List Nat := [4401,4412,4413,4444,4446,4456,4458,4472,4473,4484,4485,4510,4512,4516,4518,4596,4597,4602,4603,4604,4605,4610,4611,4616,4618,4622,4624,4644,4645,4650,4651,4678]
def ridgeSupport800_006 : List Nat := [4680,4684,4686,4692,4693,4698,4699,4700,4701,4706,4707,4724,4725,4730,4731,4828,4829,4836,4837,4996,4998,5008,5010,5024,5025,5036,5037,5068,5070,5080,5082,5096]
def ridgeSupport800_007 : List Nat := [5097,5108,5109,5266,5268,5270,5272,5278,5280,5282,5284,5300,5301,5306,5307,5314,5316,5318,5320,5336,5337,5342,5343,5696,5697,5732,5733,5792,5793,6348,6349,6354]
def ridgeSupport800_008 : List Nat := [6355,6356,6357,6359,6361,6362,6363,6396,6397,6402,6403,6404,6405,6407,6409,6410,6411,6464,6465,6467,6469,6482,6483,6485,6487,6516,6517,6522,6523,6524,6525,6527]
def ridgeSupport800_009 : List Nat := [6529,6530,6531,6584,6585,6587,6589,6602,6603,6605,6607]
def ridgeSupport800_code : Nat := 0x673f39b9cbce566f73779b9cdc660f305981cbfe5f72f997bcbd65d72e9957caae54f2a5945ca1e50728190bc85642720f905c82640f2058fdc7e636f1b58d9c6be3571a98d3c6963371996a1b505996cc9641b20537e9bd4d9a6c532298d4c4a6152ee9754b5a5a52929454a0a4f526292d494a494fd67e93e99f44f6a7b13ce9e64eb67593a19d04e4a7213869c24b965c92dd96e49ee4f527593a498e4c525d92e496e4b525592a493a49924892348ae455225912484241d20a904480e4051fd8fe47ee3f51f58fa469a3491a08cf46163091798bc45aa2d115e8ae44f6279131898448a24111688a41ae0d5065832414e0a504d826412e09504582240fa07903881b406e03501580a4001ffcffa7fc3fcdfe4fed7f63fadfd4fe57f23e59f28f907c73dedef4f757ba3d8dec4f5d7ae3d6deb4f557aa3d39e98f487a33cade54f257923c41e1cf0a7843c0de04efd77e3beddf4ef577a3a99d48ea074f15acad25682b31578aba55b2ad1564ab05542a994e4a6e53229894b0a565282939498a4852228e9470a2e5162899448a224cc26513149884bf25f12ec9744b925b92d49604af25512a494c4a5252109084641c20d90688323561aa0d3c69c3491a40d146883431a08cfc67433919a0ccc66032f1970ab855a2a61528a9054606403181700a4034
def ridgeSupport800_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport800_code
def ridgeSupport800_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport800_code
def ridgeSupport800_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport800_code
def ridgeSupport800_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport800_code
def ridgeSupport800_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport800_code
def ridgeSupport800_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport800_code
def ridgeSupport800_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport800_code
def ridgeSupport800_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport800_code
def ridgeSupport800_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport800_code
def ridgeSupport800_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport800_code
def ridgeSupport800_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport800_code
def ridgeSupport800_suffix_010 : List Nat := []
def ridgeSupport800_suffix_009 : List Nat := ridgeSupport800_009 ++ ridgeSupport800_suffix_010
def ridgeSupport800_suffix_008 : List Nat := ridgeSupport800_008 ++ ridgeSupport800_suffix_009
def ridgeSupport800_suffix_007 : List Nat := ridgeSupport800_007 ++ ridgeSupport800_suffix_008
def ridgeSupport800_suffix_006 : List Nat := ridgeSupport800_006 ++ ridgeSupport800_suffix_007
def ridgeSupport800_suffix_005 : List Nat := ridgeSupport800_005 ++ ridgeSupport800_suffix_006
def ridgeSupport800_suffix_004 : List Nat := ridgeSupport800_004 ++ ridgeSupport800_suffix_005
def ridgeSupport800_suffix_003 : List Nat := ridgeSupport800_003 ++ ridgeSupport800_suffix_004
def ridgeSupport800_suffix_002 : List Nat := ridgeSupport800_002 ++ ridgeSupport800_suffix_003
def ridgeSupport800_suffix_001 : List Nat := ridgeSupport800_001 ++ ridgeSupport800_suffix_002
def ridgeSupport800_suffix_000 : List Nat := ridgeSupport800_000 ++ ridgeSupport800_suffix_001
theorem ridgeSupport800_source : candidateSupports 800 =
    (PackedRawNatGrowth.readList 13 299 ridgeSupport800_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
