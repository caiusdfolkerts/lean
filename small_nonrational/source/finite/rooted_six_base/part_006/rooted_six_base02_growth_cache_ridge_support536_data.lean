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
def ridgeSupport536_000 : List Nat := [70,73,75,76,333,1013,1015,1018,1019,1021,1037,1039,1042,1043,1045,1049,1051,1054,1055,1057,1082,1083,1085,1086,1089,1090,1091,1093,1094,1096,1101,1102]
def ridgeSupport536_001 : List Nat := [1103,1104,1106,1107,1110,1111,1112,1114,1115,1117,1122,1123,1124,1125,1127,1128,1131,1132,1133,1135,1136,1138,1143,1144,3408,3409,3414,3415,3420,3421,3422,3423]
def ridgeSupport536_002 : List Nat := [3424,3425,3426,3427,3432,3433,3438,3439,3444,3445,3446,3447,3448,3449,3450,3451,3470,3471,3472,3473,3474,3475,3494,3495,3496,3497,3498,3499,3518,3519,3520,3521]
def ridgeSupport536_003 : List Nat := [3522,3523,3542,3543,3544,3545,3546,3547,3566,3567,3568,3569,3570,3571,3590,3591,3592,3593,3594,3595,3596,3598,3602,3604,3608,3610,3614,3615,3616,3617,3618,3619]
def ridgeSupport536_004 : List Nat := [3676,3680,3685,3687,3689,3691,3708,3712,3717,3719,3721,3723,3724,3728,3733,3735,3737,3739,4920,4921,4932,4933,4956,4957,4968,4969,4976,4978,4982,4984,4992,4993]
def ridgeSupport536_005 : List Nat := [5004,5005,5028,5029,5040,5041,5048,5050,5054,5056,5064,5065,5076,5077,5100,5101,5112,5113,5120,5122,5126,5128,6360,6361,6364,6365,6366,6367,6372,6373,6376,6377]
def ridgeSupport536_006 : List Nat := [6378,6379,6398,6399,6400,6401,6402,6403,6422,6423,6424,6425,6426,6427,6428,6430,6434,6436,6440,6442,6446,6447,6448,6449,6450,6451,6452,6454,6458,6460,6464,6466]
def ridgeSupport536_007 : List Nat := [6470,6471,6472,6473,6474,6475,6477,6478,6480,6481,6483,6484,6496,6498,6504,6506,6508,6510,7206,7207,7218,7219,7226,7228,7232,7234,7242,7243,7245,7247,7254,7255]
def ridgeSupport536_008 : List Nat := [7260,7261,7272,7273,7280,7282,7286,7288,7296,7297,7299,7301,7308,7309,7314,7315,7326,7327,7334,7336,7340,7342,7350,7351,7353,7355,7362,7363,7488,7489,7492,7493]
def ridgeSupport536_009 : List Nat := [7494,7495,7566,7567,7572,7573,7578,7579,7862,7863,7864,7865,7866,7867,7888,7896,7900]
def ridgeSupport536_code : Nat := 0x1edcf6c7b43d77ebaf5cfae3d6feb6ecdf66bb2bd94ec7f63ba8fd46ea2f513a83d40e61f30b977cb9e5bf2db95dcace54729b93fc9ee49f24b91bc8ce42f20f903c80e3c71db8e5c70e34f1a38bbc5ce2bf15b89fc4de25f12b885c40e1e70eb867c32e13f09b2dd96ccb565a32c5960caa654f2a3950ca7653729794aca4e52328f946ca1650327993ac9b64d3267932c98e4c325f92ec9564a3249922c8f647323791ac8ce46322f916c81e40b203900c7fe3fb1d78eac74e3a31cb8e4c6fe37b1bb8dcc6ce362811406a0150027f33f89f6cfb27ab3d49e4cf227813be9dd4ee27633b09d2ce9271b38c9c0ce026f13769b94dc26d33689aecd7268b34499ccce1d36e9974bba55d20e8c745ba25d0ee8574039f1cd6e69733b995cc0e5c711b889c42e2070fb879c34e1870a3849c1ce0c705b829c12e08703b819be6df26f8b7c1bdedee6edb769bb2dd86ebb759b86dc26e0b701b7edbe6d5b6a9b52da86d3b699b26d926c8b641b1ed8e6bdb5e9af2d786bbb5d9aead746b7b5b9ad2d686b1b589ac2d606afb579abad5c6abb559aa2d5023c11dc8e447023791b48d846b234119c8ca46423191888ba45b22d11608ae45622991488a044f2271134890446222910c88444121f10f487643a210907c83c41b20c905482641220790347fa3fb1fd0fdc7ea14d026012c092046
def ridgeSupport536_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport536_code
def ridgeSupport536_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport536_code
def ridgeSupport536_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport536_code
def ridgeSupport536_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport536_code
def ridgeSupport536_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport536_code
def ridgeSupport536_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport536_code
def ridgeSupport536_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport536_code
def ridgeSupport536_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport536_code
def ridgeSupport536_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport536_code
def ridgeSupport536_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport536_code
def ridgeSupport536_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport536_code
def ridgeSupport536_suffix_010 : List Nat := []
def ridgeSupport536_suffix_009 : List Nat := ridgeSupport536_009 ++ ridgeSupport536_suffix_010
def ridgeSupport536_suffix_008 : List Nat := ridgeSupport536_008 ++ ridgeSupport536_suffix_009
def ridgeSupport536_suffix_007 : List Nat := ridgeSupport536_007 ++ ridgeSupport536_suffix_008
def ridgeSupport536_suffix_006 : List Nat := ridgeSupport536_006 ++ ridgeSupport536_suffix_007
def ridgeSupport536_suffix_005 : List Nat := ridgeSupport536_005 ++ ridgeSupport536_suffix_006
def ridgeSupport536_suffix_004 : List Nat := ridgeSupport536_004 ++ ridgeSupport536_suffix_005
def ridgeSupport536_suffix_003 : List Nat := ridgeSupport536_003 ++ ridgeSupport536_suffix_004
def ridgeSupport536_suffix_002 : List Nat := ridgeSupport536_002 ++ ridgeSupport536_suffix_003
def ridgeSupport536_suffix_001 : List Nat := ridgeSupport536_001 ++ ridgeSupport536_suffix_002
def ridgeSupport536_suffix_000 : List Nat := ridgeSupport536_000 ++ ridgeSupport536_suffix_001
theorem ridgeSupport536_source : candidateSupports 536 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport536_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
