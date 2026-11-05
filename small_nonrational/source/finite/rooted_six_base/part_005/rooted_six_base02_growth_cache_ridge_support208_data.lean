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
def ridgeSupport208_000 : List Nat := [57,71,87,93,94,880,881,885,887,888,892,894,895,897,901,902,906,908,909,913,915,916,918,989,990,993,994,997,998,1061,1062,1066]
def ridgeSupport208_001 : List Nat := [1068,1069,1073,1075,1076,1078,1082,1083,1087,1089,1090,1094,1096,1097,1099,1256,1257,1258,1261,1262,1263,1265,1270,1272,1277,1278,1279,1282,1283,1284,1286,1291]
def ridgeSupport208_002 : List Nat := [1293,1340,1341,1343,1344,1345,1346,1348,1349,1351,1352,1354,1355,3177,3179,3183,3185,3236,3237,3242,3243,3263,3265,3269,3271,3276,3277,3282,3283,3284,3285,3290]
def ridgeSupport208_003 : List Nat := [3291,3332,3333,3338,3339,3345,3347,3351,3353,3372,3373,3378,3379,3396,3397,3402,3403,3417,3419,3423,3425,3476,3477,3482,3483,3503,3505,3509,3511,3516,3517,3522]
def ridgeSupport208_004 : List Nat := [3523,3524,3525,3530,3531,3572,3573,3578,3579,3585,3587,3591,3593,3612,3613,3618,3619,3636,3637,3642,3643,3648,3649,3652,3653,4545,4547,4551,4553,4556,4557,4562]
def ridgeSupport208_005 : List Nat := [4563,4604,4605,4610,4611,4631,4633,4637,4639,4644,4645,4650,4651,4652,4653,4658,4659,4665,4667,4671,4673,4700,4701,4706,4707,4724,4725,4730,4731,4752,4753,4760]
def ridgeSupport208_006 : List Nat := [4761,4845,4847,4875,4877,4890,4891,4908,4909,4917,4919,4947,4949,4962,4963,4980,4981,6227,6229,6231,6233,6251,6253,6257,6259,6264,6265,6270,6271,6272,6273,6278]
def ridgeSupport208_007 : List Nat := [6279,6312,6313,6318,6319,6320,6321,6326,6327,6333,6335,6339,6341,6351,6352,6354,6355,6359,6361,6363,6365,6383,6385,6389,6391,6396,6397,6402,6403,6404,6405,6410]
def ridgeSupport208_008 : List Nat := [6411,6444,6445,6450,6451,6452,6453,6458,6459,6465,6467,6471,6473,6483,6484,6486,6487,6490,6491,7007,7009,7011,7013,7016,7017,7022,7023,7043,7045,7049,7051,7056]
def ridgeSupport208_009 : List Nat := [7057,7062,7063,7064,7065,7070,7071,7077,7079,7083,7085,7104,7105,7110,7111,7112,7113,7115,7116,7126,7127,7149,7151,7158,7159,7176,7177,7179,7181,7194,7195,7196]
def ridgeSupport208_010 : List Nat := [7198,7203,7205,7212,7213,7230,7231,7233,7235,7248,7249,7250,7252,7475,7477,7479,7481,7487,7489,7491,7493,7546,7548,7550,7552,7557,7559,7563,7565,7842,7843,7878]
def ridgeSupport208_011 : List Nat := [7879,8024,8025]
def ridgeSupport208_code : Nat := 0x7d67eb1ec7f637a8fd45d8dec5f61fb0bd80ebf75f3af5d45ea1f507a7fd39e9bf4d7a67c54e2971478a1c43e20f0ff87dc2de167097847c1ee0e706f835c0de05f027811bf7dfb6fbf7dbbd7deb6f33797bc9de46f1f78dbc1de06eb7757ba7dd2ee7f73db99dcc6e5f72db91dc86e2f713b85dc1edbf6ddb69db46d976c7b61dafe56f2b5957cab65532a7949ca3e50f28393bc9d64d7269933c9964b725990bc856417209903c8163f71f98f7c7ae3c71df8ddc6de3671af8d3c69634319f8c5c61e2ff17b8b7c5b62c71618afc5762a7151887c43620710187fc3f61e70f1873c38e1b70d7859c2be1570a73759ba4d8e6c53559a9ccde66b32d9964c6e63530d985cbbe5db29994c4a4652127b93d49d64e926393149764b924191fc8ee47323391948b645922b915489644921f90ec86642f20390147f63f91d38e947363991c98e3c70e382e457223905c80e3b71d38d5c68e237113875c38e09703b80dc02dfb6fd37d5be8dcb6e53715b88dc36e136f5b78db76dab6c5b5ed9b6cd3655b28d616afb56dab2d4b6a53515a88d3369934b5a58d1968bb44da22d0b6853415a08cdb66d33559a8cd36693335998cc7662b30597ecab6553295948c71637b1ad8d254b2a51520a8e5452a21508a8254029f94f4a7850d2859418a0850328113fc9fc4fd27c13d89e24ef27713b49d44e9274112c892448223110888243f21d90e886c43421990c485a42c215109884a3e61f28f887c23de1ee8e587283931c88e3471838a1c30e1470237f1bf0df06f03771ba8dc46e005e02e815c08e039
def ridgeSupport208_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport208_code
def ridgeSupport208_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport208_code
def ridgeSupport208_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport208_code
def ridgeSupport208_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport208_code
def ridgeSupport208_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport208_code
def ridgeSupport208_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport208_code
def ridgeSupport208_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport208_code
def ridgeSupport208_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport208_code
def ridgeSupport208_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport208_code
def ridgeSupport208_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport208_code
def ridgeSupport208_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport208_code
def ridgeSupport208_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport208_code
def ridgeSupport208_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport208_code
def ridgeSupport208_suffix_012 : List Nat := []
def ridgeSupport208_suffix_011 : List Nat := ridgeSupport208_011 ++ ridgeSupport208_suffix_012
def ridgeSupport208_suffix_010 : List Nat := ridgeSupport208_010 ++ ridgeSupport208_suffix_011
def ridgeSupport208_suffix_009 : List Nat := ridgeSupport208_009 ++ ridgeSupport208_suffix_010
def ridgeSupport208_suffix_008 : List Nat := ridgeSupport208_008 ++ ridgeSupport208_suffix_009
def ridgeSupport208_suffix_007 : List Nat := ridgeSupport208_007 ++ ridgeSupport208_suffix_008
def ridgeSupport208_suffix_006 : List Nat := ridgeSupport208_006 ++ ridgeSupport208_suffix_007
def ridgeSupport208_suffix_005 : List Nat := ridgeSupport208_005 ++ ridgeSupport208_suffix_006
def ridgeSupport208_suffix_004 : List Nat := ridgeSupport208_004 ++ ridgeSupport208_suffix_005
def ridgeSupport208_suffix_003 : List Nat := ridgeSupport208_003 ++ ridgeSupport208_suffix_004
def ridgeSupport208_suffix_002 : List Nat := ridgeSupport208_002 ++ ridgeSupport208_suffix_003
def ridgeSupport208_suffix_001 : List Nat := ridgeSupport208_001 ++ ridgeSupport208_suffix_002
def ridgeSupport208_suffix_000 : List Nat := ridgeSupport208_000 ++ ridgeSupport208_suffix_001
theorem ridgeSupport208_source : candidateSupports 208 =
    (PackedRawNatGrowth.readList 13 355 ridgeSupport208_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
