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
def ridgeSupport336_000 : List Nat := [58,72,88,93,95,880,882,884,886,888,893,894,896,899,922,923,927,929,930,934,936,937,939,1001,1002,1005,1006,1009,1010,1061,1063,1065]
def ridgeSupport336_001 : List Nat := [1067,1069,1074,1075,1077,1080,1103,1104,1108,1110,1111,1115,1117,1118,1120,1255,1257,1259,1260,1262,1264,1265,1269,1274,1298,1299,1300,1303,1304,1305,1307,1312]
def ridgeSupport336_002 : List Nat := [1314,1339,1341,1342,1344,1345,1347,1349,1350,1352,1353,1357,1358,3171,3173,3182,3187,3238,3239,3248,3249,3261,3264,3270,3271,3275,3277,3280,3281,3286,3287,3296]
def ridgeSupport336_003 : List Nat := [3297,3334,3335,3339,3341,3344,3345,3350,3355,3366,3367,3376,3377,3390,3391,3400,3401,3411,3413,3422,3427,3478,3479,3488,3489,3501,3504,3510,3511,3515,3517,3520]
def ridgeSupport336_004 : List Nat := [3521,3526,3527,3536,3537,3574,3575,3579,3581,3584,3585,3590,3595,3606,3607,3616,3617,3630,3631,3640,3641,3664,3665,3668,3669,4539,4541,4550,4555,4558,4559,4568]
def ridgeSupport336_005 : List Nat := [4569,4606,4607,4616,4617,4629,4632,4638,4639,4643,4645,4648,4649,4654,4655,4659,4661,4664,4665,4670,4675,4702,4703,4712,4713,4726,4727,4736,4737,4768,4769,4776]
def ridgeSupport336_006 : List Nat := [4777,4844,4849,4874,4879,4888,4889,4906,4907,4989,4991,5019,5021,5034,5035,5052,5053,5241,5244,5247,5251,5253,5256,5259,5263,5312,5317,5318,5322,5324,5329,5337]
def ridgeSupport336_007 : List Nat := [5339,5608,5609,5644,5645,5794,5795,6238,6239,6248,6249,6262,6263,6266,6268,6269,6270,6286,6287,6296,6297,6310,6311,6314,6316,6317,6318,6501,6504,6515,6517,6538]
def ridgeSupport336_008 : List Nat := [6539,6542,6544,6545,6546,6555,6556,6557,6558,6590,6592,6594,6595]
def ridgeSupport336_code : Nat := 0x19c3ce1670337d99eccee673337992cc8e64331d98bcc565d72e7968cb2e2bb15b8acc55629f14d899c4c623f11d87ec3ee1f30f5877c3b61a70d185fc2f5a8ed4560db0657a6bd14dba6cd3469994caa63531698148fa45d22290b483a3fd1f28f33bd9de4eae75539d9cdcdfe6fb32b9954c6663130f9854bc65d92a99544a8654128194049de4ed269934497e4bd24391f48e6471235919c8be45d229914489644721f90f486242b20990447fe3fd1d98ec473e39d1cb8e346f6376e5572a3945ca0e3971c38bdc5ce21710385dc2ce0b7033805c00dfd6fdb7ddbecdd16e8371db8cdc16e036f5b76db76db36c1b5ada16d0365db2cd636af3555aa6d496a434fda7cd31698349da4cd1b68b3445a20d0d685b41da0cce1670335d9accd16683335996cc7663330197acb1658329d94cc7363731958c654e2a69524a905462a2950ca8254029f14f4a76522290146ca3251828b9450a2651227d13d49e24f027713b09d64e927391808bc45d22d915c8ac454228113c87043521990c885a42b214909c84a3f21f88fb87da3ea1f48eac7523a81d30e8874239f1cd8e687063801bf0df46f03761ba0dc86e005f02e816009003a
def ridgeSupport336_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport336_code
def ridgeSupport336_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport336_code
def ridgeSupport336_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport336_code
def ridgeSupport336_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport336_code
def ridgeSupport336_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport336_code
def ridgeSupport336_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport336_code
def ridgeSupport336_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport336_code
def ridgeSupport336_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport336_code
def ridgeSupport336_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport336_code
def ridgeSupport336_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport336_code
def ridgeSupport336_suffix_009 : List Nat := []
def ridgeSupport336_suffix_008 : List Nat := ridgeSupport336_008 ++ ridgeSupport336_suffix_009
def ridgeSupport336_suffix_007 : List Nat := ridgeSupport336_007 ++ ridgeSupport336_suffix_008
def ridgeSupport336_suffix_006 : List Nat := ridgeSupport336_006 ++ ridgeSupport336_suffix_007
def ridgeSupport336_suffix_005 : List Nat := ridgeSupport336_005 ++ ridgeSupport336_suffix_006
def ridgeSupport336_suffix_004 : List Nat := ridgeSupport336_004 ++ ridgeSupport336_suffix_005
def ridgeSupport336_suffix_003 : List Nat := ridgeSupport336_003 ++ ridgeSupport336_suffix_004
def ridgeSupport336_suffix_002 : List Nat := ridgeSupport336_002 ++ ridgeSupport336_suffix_003
def ridgeSupport336_suffix_001 : List Nat := ridgeSupport336_001 ++ ridgeSupport336_suffix_002
def ridgeSupport336_suffix_000 : List Nat := ridgeSupport336_000 ++ ridgeSupport336_suffix_001
theorem ridgeSupport336_source : candidateSupports 336 =
    (PackedRawNatGrowth.readList 13 269 ridgeSupport336_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
