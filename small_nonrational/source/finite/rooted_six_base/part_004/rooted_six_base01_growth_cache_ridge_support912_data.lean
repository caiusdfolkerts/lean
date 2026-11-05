module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport912_000 : List Nat := [925,926,927,1262,1263,1264,1567,1568,1569,1589,1590,1591,4506,4507,4508,4509,4510,4511,4602,4603,4604,4605,4606,4607,4698,4699,4700,4701,4702,4703,4770,4771]
def ridgeSupport912_001 : List Nat := [4772,4773,4774,4775,4866,4867,4868,4869,4870,4871,4962,4963,4964,4965,4966,4967,5364,5365,5366,5367,5368,5369,5376,5377,5378,5379,5380,5381,6450,6451,6452,6453]
def ridgeSupport912_002 : List Nat := [6454,6455,6498,6499,6500,6501,6502,6503,6642,6643,6644,6645,6646,6647,7014,7015,7016,7017,7018,7019,7044,7045,7046,7047,7048,7049,9480,9481,9486,9487,9492,9493]
def ridgeSupport912_003 : List Nat := [9507,9509,9513,9515,9519,9521,9528,9529,9534,9535,9540,9541,9627,9629,9633,9635,9639,9641,9675,9677,9681,9683,9687,9689,9720,9721,9726,9727,9732,9733,9747,9749]
def ridgeSupport912_004 : List Nat := [9753,9755,9759,9761,9768,9769,9774,9775,9780,9781,9867,9869,9873,9875,9879,9881,9915,9917,9921,9923,9927,9929,10212,10213,10214,10215,10216,10217,10224,10225,10226,10227]
def ridgeSupport912_005 : List Nat := [10228,10229,11019,11021,11025,11027,11031,11033,11040,11041,11046,11047,11052,11053,11088,11089,11094,11095,11100,11101,11187,11189,11193,11195,11199,11201,11202,11203,11204,11205,11206,11207]
def ridgeSupport912_006 : List Nat := [11502,11503,11504,11505,11506,11507,11532,11533,11534,11535,11536,11537,13093,13095,13097,13155,13157,13161,13163,13167,13169,13225,13227,13229,13287,13289,13293,13295,13299,13301,13542,13543]
def ridgeSupport912_007 : List Nat := [13544,13545,13546,13547,14041,14043,14045,14139,14141,14145,14147,14151,14153,14364,14365,14366,14367,14368,14369,14976,14977,14982,14983,14988,14989,15012,15013,15018,15019,15024,15025,15170]
def ridgeSupport912_008 : List Nat := [15172,15176,15178,15182,15184]
def ridgeSupport912_code : Nat := 0x3b50ed3bb4aed23b44ed0bab1eac3aabeaabaa5ea93a8dea33a87ea1ba81ea03821e08381fe07b81de073749dd1f743dd0773ddcef6dddb6f6d9d3af4ead3a74e8d39f4e6cfd73f3cfbf3edcfa73e7ceb73abcea7371cdbf36bcda7365cd8f329cc9f325b446d10b43ed0eb436d0cb3cecf2b3c6cf0b3beceeaf1ebc6af16bc4af0ebc2af06bbfaeeebb9aed6bb3ad76b5cad5eb56ad46b50acb6b2cac9eb26ac86b20ac66b17ac4eb11ac36b0b9fd67f49fce7f29fc67f09fa67e89f9e7e69f967e49b266c79b0e6c19af66bb9a666979a4e6919a3668b98d663498be62e98a6628988661f986e6199856613981660497fe5fe97e65f897665d7974e5d197365cb96a65a7968e5a1967659b951654494fe53e94e653894c652f94ae52994965239456514943e50e94265086e25b886e1db866e15b846dadb6a6da5b686d9db6667dd9f667d59f467cd9f2659d9666595964658d96264dd93664d593464cd9325415504540d502540550053e54f853dd4f653d54f44d9d3664d953644d8d3624c1d3064c153044c0d3024a9d2a64a952a44a8d2a2497d25e497525c496d25a47fd1fe47f51fc47ed1fa467d19e467519c466d19a18dc63618d4621188061f13c04ef13b839f0e7839d
def ridgeSupport912_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport912_code
def ridgeSupport912_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport912_code
def ridgeSupport912_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport912_code
def ridgeSupport912_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport912_code
def ridgeSupport912_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport912_code
def ridgeSupport912_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport912_code
def ridgeSupport912_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport912_code
def ridgeSupport912_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport912_code
def ridgeSupport912_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport912_code
def ridgeSupport912_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport912_code
def ridgeSupport912_suffix_009 : List Nat := []
def ridgeSupport912_suffix_008 : List Nat := ridgeSupport912_008 ++ ridgeSupport912_suffix_009
def ridgeSupport912_suffix_007 : List Nat := ridgeSupport912_007 ++ ridgeSupport912_suffix_008
def ridgeSupport912_suffix_006 : List Nat := ridgeSupport912_006 ++ ridgeSupport912_suffix_007
def ridgeSupport912_suffix_005 : List Nat := ridgeSupport912_005 ++ ridgeSupport912_suffix_006
def ridgeSupport912_suffix_004 : List Nat := ridgeSupport912_004 ++ ridgeSupport912_suffix_005
def ridgeSupport912_suffix_003 : List Nat := ridgeSupport912_003 ++ ridgeSupport912_suffix_004
def ridgeSupport912_suffix_002 : List Nat := ridgeSupport912_002 ++ ridgeSupport912_suffix_003
def ridgeSupport912_suffix_001 : List Nat := ridgeSupport912_001 ++ ridgeSupport912_suffix_002
def ridgeSupport912_suffix_000 : List Nat := ridgeSupport912_000 ++ ridgeSupport912_suffix_001
theorem ridgeSupport912_source : candidateRows 912 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport912_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
