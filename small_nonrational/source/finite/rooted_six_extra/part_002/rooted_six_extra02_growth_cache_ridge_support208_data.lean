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
def ridgeSupport208_000 : List Nat := [57,71,87,93,94,880,881,885,887,888,892,894,895,897,901,902,906,908,909,913,915,916,918,989,990,993,994,997,998,1061,1062,1066]
def ridgeSupport208_001 : List Nat := [1068,1069,1073,1075,1076,1078,1082,1083,1087,1089,1090,1094,1096,1097,1099,1256,1257,1258,1261,1262,1263,1265,1270,1272,1277,1278,1279,1282,1283,1284,1286,1291]
def ridgeSupport208_002 : List Nat := [1293,1340,1341,1343,1344,1345,1346,1348,1349,1351,1352,1354,1355,3177,3179,3183,3185,3236,3237,3242,3243,3263,3265,3269,3271,3276,3277,3282,3283,3284,3285,3290]
def ridgeSupport208_003 : List Nat := [3291,3332,3333,3338,3339,3345,3347,3351,3353,3372,3373,3378,3379,3396,3397,3402,3403,3417,3419,3423,3425,3476,3477,3482,3483,3503,3505,3509,3511,3516,3517,3522]
def ridgeSupport208_004 : List Nat := [3523,3524,3525,3530,3531,3572,3573,3578,3579,3585,3587,3591,3593,3612,3613,3618,3619,3636,3637,3642,3643,3648,3649,3652,3653,4545,4547,4551,4553,4556,4557,4562]
def ridgeSupport208_005 : List Nat := [4563,4604,4605,4610,4611,4631,4633,4637,4639,4644,4645,4650,4651,4652,4653,4658,4659,4665,4667,4671,4673,4700,4701,4706,4707,4724,4725,4730,4731,4752,4753,4760]
def ridgeSupport208_006 : List Nat := [4761,4845,4847,4875,4877,4890,4891,4908,4909,4917,4919,4947,4949,4962,4963,4980,4981,5243,5245,5247,5249,5255,5257,5259,5261,5314,5316,5318,5320,5325,5327,5331]
def ridgeSupport208_007 : List Nat := [5333,5610,5611,5646,5647,5792,5793,6236,6237,6242,6243,6260,6261,6266,6267,6270,6271,6284,6285,6290,6291,6308,6309,6314,6315,6318,6319,6503,6505,6509,6511,6536]
def ridgeSupport208_008 : List Nat := [6537,6542,6543,6546,6547,6554,6556,6558,6559,6572,6574,6576,6577]
def ridgeSupport208_code : Nat := 0x19b1cd866bb35999fccf6673335993cc9663f31d989cc465bf2db969cb3e2bf15d8abc556297149893c49623711987fc3f61ef0f5875c3a618f0c585dc2e5a86d4160fb0757aebd54d5a69d33e99b4c8a63531298548da45d22690f481a3fd1f68f73759ba4d8e6c53559a9ccde66b32d9964c6e63530d985cbbe5db29994c4a4652127b93d49d64e926393149764b924191fc8ee47323391948b645922b915489644921f90ec86642f20390147f63f91d38e947363991c98e3c70e382e457223905c80e3b71d38d5c68e237113875c38e09703b80dc02dfb6fd37d5be8dcb6e53715b88dc36e136f5b78db76dab6c5b5ed9b6cd3655b28d616afb56dab2d4b6a53515a88d3369934b5a58d1968bb44da22d0b6853415a08cdb66d33559a8cd36693335998cc7662b30597ecab6553295948c71637b1ad8d254b2a51520a8e5452a21508a8254029f94f4a7850d2859418a0850328113fc9fc4fd27c13d89e24ef27713b49d44e9274112c892448223110888243f21d90e886c43421990c485a42c215109884a3e61f28f887c23de1ee8e587283931c88e3471838a1c30e1470237f1bf0df06f03771ba8dc46e005e02e815c08e039
def ridgeSupport208_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport208_code
def ridgeSupport208_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport208_code
def ridgeSupport208_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport208_code
def ridgeSupport208_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport208_code
def ridgeSupport208_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport208_code
def ridgeSupport208_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport208_code
def ridgeSupport208_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport208_code
def ridgeSupport208_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport208_code
def ridgeSupport208_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport208_code
def ridgeSupport208_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport208_code
def ridgeSupport208_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 269 ridgeSupport208_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
