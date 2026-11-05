module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport336_000 : List Nat := [58,72,88,93,95,880,882,884,886,888,893,894,896,899,922,923,927,929,930,934,936,937,939,1001,1002,1005,1006,1009,1010,1061,1063,1065]
def ridgeSupport336_001 : List Nat := [1067,1069,1074,1075,1077,1080,1103,1104,1108,1110,1111,1115,1117,1118,1120,1255,1257,1259,1260,1262,1264,1265,1269,1274,1298,1299,1300,1303,1304,1305,1307,1312]
def ridgeSupport336_002 : List Nat := [1314,1339,1341,1342,1344,1345,1347,1349,1350,1352,1353,1357,1358,3171,3173,3182,3187,3238,3239,3248,3249,3261,3264,3270,3271,3275,3277,3280,3281,3286,3287,3296]
def ridgeSupport336_003 : List Nat := [3297,3334,3335,3339,3341,3344,3345,3350,3355,3366,3367,3376,3377,3390,3391,3400,3401,3411,3413,3422,3427,3478,3479,3488,3489,3501,3504,3510,3511,3515,3517,3520]
def ridgeSupport336_004 : List Nat := [3521,3526,3527,3536,3537,3574,3575,3579,3581,3584,3585,3590,3595,3606,3607,3616,3617,3630,3631,3640,3641,3664,3665,3668,3669,4539,4541,4550,4555,4558,4559,4568]
def ridgeSupport336_005 : List Nat := [4569,4606,4607,4616,4617,4629,4632,4638,4639,4643,4645,4648,4649,4654,4655,4659,4661,4664,4665,4670,4675,4702,4703,4712,4713,4726,4727,4736,4737,4768,4769,4776]
def ridgeSupport336_006 : List Nat := [4777,4844,4849,4874,4879,4888,4889,4906,4907,4989,4991,5019,5021,5034,5035,5052,5053,6225,6228,6231,6235,6249,6252,6258,6259,6263,6265,6268,6269,6274,6275,6284]
def ridgeSupport336_007 : List Nat := [6285,6306,6307,6316,6317,6322,6323,6327,6329,6332,6333,6338,6343,6348,6349,6353,6355,6357,6360,6363,6367,6381,6384,6390,6391,6395,6397,6400,6401,6406,6407,6416]
def ridgeSupport336_008 : List Nat := [6417,6438,6439,6448,6449,6454,6455,6459,6461,6464,6465,6470,6475,6480,6481,6485,6487,6494,6495,7005,7008,7011,7015,7018,7019,7028,7029,7041,7044,7050,7051,7055]
def ridgeSupport336_009 : List Nat := [7057,7060,7061,7066,7067,7071,7073,7076,7077,7082,7087,7098,7099,7108,7109,7112,7114,7118,7119,7130,7131,7148,7153,7156,7157,7174,7175,7178,7183,7192,7193,7197]
def ridgeSupport336_010 : List Nat := [7200,7257,7259,7266,7267,7284,7285,7287,7289,7302,7303,7304,7306,7473,7476,7479,7483,7485,7488,7491,7495,7544,7549,7550,7554,7556,7561,7569,7571,7840,7841,7876]
def ridgeSupport336_011 : List Nat := [7877,8026,8027]
def ridgeSupport336_code : Nat := 0x7d6feb5ec5f627a87d41d93ec8f627b09d82ebf75f7af1d47ea1f503a7bd3be9bf4d3a63c8ae44721f90dc79e3bf1d78e9c63e31716f8b3c20e0ef067831c0fe05701f80dbf5dfa6fc77d9bdbded6f3f79dbcade46f17789bbbddd6ebf755ba5dd26e8773fb9bdcd6e57729b91dc7ee2f715b84dc0edd76e9b6bdb56d9f6c7b60daee57f2bd957caae5472a194bca3650728193dc9de4df26d931c98649f24d911c88641f20d901c8063f71f78f7c7b63c31db8dfc6de3631ab8d3c68e3371998c7c6162f71798b9c5be2cf1658adc56628f14588dc46620f10587dc3e61e70ef873c3961b30d385bc2be1530a33bd9de4eae75539d9cdcdfe6fb32b9954c6663130f9854bc65d92a99544a8654128194049de4ed269934497e4bd24391f48e6471235919c8be45d229914489644721f90f486242b20990447fe3fd1d98ec473e39d1cb8e346f6376e5572a3945ca0e3971c38bdc5ce21710385dc2ce0b7033805c00dfd6fdb7ddbecdd16e8371db8cdc16e036f5b76db76db36c1b5ada16d0365db2cd636af3555aa6d496a434fda7cd31698349da4cd1b68b3445a20d0d685b41da0cce1670335d9accd16683335996cc7663330197acb1658329d94cc7363731958c654e2a69524a905462a2950ca8254029f14f4a76522290146ca3251828b9450a2651227d13d49e24f027713b09d64e927391808bc45d22d915c8ac454228113c87043521990c885a42b214909c84a3f21f88fb87da3ea1f48eac7523a81d30e8874239f1cd8e687063801bf0df46f03761ba0dc86e005f02e816009003a
def ridgeSupport336_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport336_code
def ridgeSupport336_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport336_code
def ridgeSupport336_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport336_code
def ridgeSupport336_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport336_code
def ridgeSupport336_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport336_code
def ridgeSupport336_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport336_code
def ridgeSupport336_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport336_code
def ridgeSupport336_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport336_code
def ridgeSupport336_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport336_code
def ridgeSupport336_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport336_code
def ridgeSupport336_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport336_code
def ridgeSupport336_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport336_code
def ridgeSupport336_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport336_code
def ridgeSupport336_suffix_012 : List Nat := []
def ridgeSupport336_suffix_011 : List Nat := ridgeSupport336_011 ++ ridgeSupport336_suffix_012
def ridgeSupport336_suffix_010 : List Nat := ridgeSupport336_010 ++ ridgeSupport336_suffix_011
def ridgeSupport336_suffix_009 : List Nat := ridgeSupport336_009 ++ ridgeSupport336_suffix_010
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
    (PackedRawNatGrowth.readList 13 355 ridgeSupport336_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
