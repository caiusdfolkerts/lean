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
def ridgeSupport88_000 : List Nat := [67,71,72,73,330,990,992,993,996,998,1002,1004,1005,1008,1010,1014,1016,1017,1020,1022,1062,1063,1065,1066,1067,1068,1070,1071,1073,1074,1076,1077]
def ridgeSupport88_001 : List Nat := [1083,1084,1086,1087,1088,1089,1091,1092,1094,1095,1097,1098,1104,1105,1107,1108,1109,1110,1112,1113,1115,1116,1118,1119,3404,3405,3406,3407,3408,3409,3410,3411]
def ridgeSupport88_002 : List Nat := [3416,3417,3422,3423,3428,3429,3430,3431,3432,3433,3434,3435,3440,3441,3446,3447,3452,3453,3454,3455,3456,3457,3476,3477,3478,3479,3480,3481,3500,3501,3502,3503]
def ridgeSupport88_003 : List Nat := [3504,3505,3524,3525,3526,3527,3528,3529,3548,3549,3550,3551,3552,3553,3572,3573,3574,3575,3576,3577,3596,3597,3598,3599,3600,3601,3605,3607,3611,3613,3617,3619]
def ridgeSupport88_004 : List Nat := [3645,3649,3652,3654,3656,3658,3661,3665,3668,3670,3672,3674,3677,3681,3684,3686,3688,3690,4844,4845,4856,4857,4880,4881,4892,4893,4907,4909,4913,4915,4916,4917]
def ridgeSupport88_005 : List Nat := [4928,4929,4952,4953,4964,4965,4979,4981,4985,4987,4988,4989,5000,5001,5024,5025,5036,5037,5051,5053,5057,5059,6356,6357,6358,6359,6360,6361,6368,6369,6370,6371]
def ridgeSupport88_006 : List Nat := [6372,6373,6380,6381,6382,6383,6384,6385,6404,6405,6406,6407,6408,6409,6428,6429,6430,6431,6432,6433,6437,6439,6443,6445,6449,6451,6452,6453,6454,6455,6456,6457]
def ridgeSupport88_007 : List Nat := [6461,6463,6467,6469,6473,6475,6479,6480,6482,6483,6485,6486,6489,6491,6493,6495,6497,6499,7148,7149,7160,7161,7175,7177,7181,7183,7184,7185,7192,7194,7196,7197]
def ridgeSupport88_008 : List Nat := [7202,7203,7214,7215,7229,7231,7235,7237,7238,7239,7246,7248,7250,7251,7256,7257,7268,7269,7283,7285,7289,7291,7292,7293,7300,7302,7304,7305,7484,7485,7486,7487]
def ridgeSupport88_009 : List Nat := [7488,7489,7556,7557,7562,7563,7568,7569,7844,7845,7846,7847,7848,7849,7881,7885,7889]
def ridgeSupport88_code : Nat := 0x1ed1f66fb27d53ea8f53fa9bd4bea4ec8f643b17d8aec2f613a83d40e9ff4fba7bd3ce44f22390dc84e3ef1f38f7c79e3af1cf8cbc64e2cf1638a7c52e28713b88fc46e22f10f87fc3de17f0bb847c22e0ef073835c18e08f04381fc0de04f01f7f3bf8df6efb32c7961cafe5772b7959cab65572a7952ca8653f297949ca2e50f27f93dc9ce4e326f936c9ae4d3267931c96e4af24f925c90e48323f91ec8ee473213908c83e41b20b904c78e3c31df8eec76e3b31cb8e4c71e38b1c38e0c6ce3631af8d6c6ae3527873c19deceee75b3ac9d0ce827133889becdf26f73799bacdce6cb3649accd6268334099accd2667331996ccae63b31c988cc425f32f8976cbb1cd4e687333991cc2e5d72d3961cace54728b935c94e487233911c82e3d711b885c3ae1b70bb855c22e10707b839c1ae0c6fcb7e1beedf66fab7d1bc2de06efb779bbaddc6e4b721b8edc66e2b711b62db06d7b6b9b5adac6ccb661b2ed966cab651b02d806bfb5f9afad7c6bbb5d9ae2d706b5b5a9ad2d686b3b599acad646afb579ab2d586a9b549aa2d506a7b539a9ad4c22f91788b845b22c91608ac45522a114c8a2450225112488e446222110c88244021f90f887843b21a90d086443121790b885842b21510a484e4261ff0ff07f23f81fb0fc87e03ed1f60fa87cc3e41f08f807bc14a024812008e043
def ridgeSupport88_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport88_code
def ridgeSupport88_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport88_code
def ridgeSupport88_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport88_code
def ridgeSupport88_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport88_code
def ridgeSupport88_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport88_code
def ridgeSupport88_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport88_code
def ridgeSupport88_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport88_code
def ridgeSupport88_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport88_code
def ridgeSupport88_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport88_code
def ridgeSupport88_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport88_code
def ridgeSupport88_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport88_code
def ridgeSupport88_suffix_010 : List Nat := []
def ridgeSupport88_suffix_009 : List Nat := ridgeSupport88_009 ++ ridgeSupport88_suffix_010
def ridgeSupport88_suffix_008 : List Nat := ridgeSupport88_008 ++ ridgeSupport88_suffix_009
def ridgeSupport88_suffix_007 : List Nat := ridgeSupport88_007 ++ ridgeSupport88_suffix_008
def ridgeSupport88_suffix_006 : List Nat := ridgeSupport88_006 ++ ridgeSupport88_suffix_007
def ridgeSupport88_suffix_005 : List Nat := ridgeSupport88_005 ++ ridgeSupport88_suffix_006
def ridgeSupport88_suffix_004 : List Nat := ridgeSupport88_004 ++ ridgeSupport88_suffix_005
def ridgeSupport88_suffix_003 : List Nat := ridgeSupport88_003 ++ ridgeSupport88_suffix_004
def ridgeSupport88_suffix_002 : List Nat := ridgeSupport88_002 ++ ridgeSupport88_suffix_003
def ridgeSupport88_suffix_001 : List Nat := ridgeSupport88_001 ++ ridgeSupport88_suffix_002
def ridgeSupport88_suffix_000 : List Nat := ridgeSupport88_000 ++ ridgeSupport88_suffix_001
theorem ridgeSupport88_source : candidateSupports 88 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport88_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
