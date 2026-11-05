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
def ridgeSupport200_000 : List Nat := [21,41,71,77,83,84,174,175,176,177,184,185,418,419,423,425,426,430,432,433,435,439,440,444,446,447,451,453,454,456,615,616]
def ridgeSupport200_001 : List Nat := [619,620,623,624,687,688,692,694,695,699,701,702,704,708,709,713,715,716,720,722,723,725,991,992,993,994,995,996,1063,1064,1065,1068]
def ridgeSupport200_002 : List Nat := [1069,1070,1072,1077,1079,1084,1085,1086,1089,1090,1091,1093,1098,1100,1147,1148,1149,1152,1153,1154,1156,1161,1163,1168,1169,1170,1173,1174,1175,1177,1182,1184]
def ridgeSupport200_003 : List Nat := [1231,1232,1234,1235,1236,1237,1239,1240,1242,1243,1245,1246,2409,2411,2415,2417,2468,2469,2474,2475,2495,2497,2501,2503,2508,2509,2514,2515,2516,2517,2522,2523]
def ridgeSupport200_004 : List Nat := [2564,2565,2570,2571,2577,2579,2583,2585,2604,2605,2610,2611,2628,2629,2634,2635,2649,2651,2655,2657,2708,2709,2714,2715,2735,2737,2741,2743,2748,2749,2754,2755]
def ridgeSupport200_005 : List Nat := [2756,2757,2762,2763,2804,2805,2810,2811,2817,2819,2823,2825,2844,2845,2850,2851,2868,2869,2874,2875,2883,2885,2895,2897,2916,2917,2928,2929,2955,2957,2967,2969]
def ridgeSupport200_006 : List Nat := [2988,2989,3000,3001,3441,3443,3447,3449,3452,3453,3458,3459,3500,3501,3506,3507,3527,3529,3533,3535,3540,3541,3546,3547,3548,3549,3554,3555,3561,3563,3567,3569]
def ridgeSupport200_007 : List Nat := [3596,3597,3602,3603,3620,3621,3626,3627,3644,3645,3656,3657,4017,4019,4023,4025,4028,4029,4034,4035,4076,4077,4082,4083,4103,4105,4109,4111,4116,4117,4122,4123]
def ridgeSupport200_008 : List Nat := [4124,4125,4130,4131,4137,4139,4143,4145,4172,4173,4178,4179,4196,4197,4202,4203,4221,4223,4251,4253,4266,4267,4284,4285,4293,4295,4323,4325,4338,4339,4356,4357]
def ridgeSupport200_009 : List Nat := [4857,4859,4869,4871,4902,4903,4914,4915,4929,4931,4941,4943,4974,4975,4986,4987,5195,5197,5199,5201,5207,5209,5211,5213,5220,5221,5226,5227,5254,5256,5258,5260]
def ridgeSupport200_010 : List Nat := [5278,5280,5282,5284,5289,5291,5295,5297,5324,5326,5330,5332,5514,5515,5550,5551,5636,5637,5732,5733,6068,6069,6074,6075,6092,6093,6098,6099,6102,6103,6116,6117]
def ridgeSupport200_011 : List Nat := [6122,6123,6140,6141,6146,6147,6150,6151,6164,6166,6168,6169,6182,6184,6186,6187,6287,6289,6293,6295,6320,6321,6326,6327,6330,6331,6383,6385,6389,6391,6416,6417]
def ridgeSupport200_012 : List Nat := [6422,6423,6426,6427,6434,6436,6438,6439,6452,6454,6456,6457,6560,6562,6564,6565,6578,6580,6582,6583]
def ridgeSupport200_code : Nat := 0xcdbe6db3699b2cd2e6933459a0c9ce4e326d934c93e49b249922c8de46b22f916c88e4431ef8f5c78e3bf1778bac5be2db1638b0c4be25712388fc15e0ab051826c0ce06302d814c03e01b007802bfedff2fd77eabf2df92faf7d6be9df4af9b7ccbdddeeaf6b7b4b32d992c0b604ad7d6bab1758aa6a534a99d4cca58d2be9574a9a52528a94149ea46522a911486a35d1aa8cb464a2ed16e8b3457a28d13e89b44b9bdcdea6df36e9a7cd36687341999ccca64f326983cc165f72f9882c4121e70f2872c38e18f0c585ec2f21570aa84ec26e0ff07d835c1aa0cb064829c14a09b04c818c0be057029811c08a03b01c80dc06a02b014807c0360130077f9bfc9fdafec7e1bf09f7afbc7dcbeddf66fb1724b921c7ae3c715b8a9c4ae24709b849c1ae0c6f8b7bdbd6de96f1b789bbaddc6edb769baadd46e7b735b92dc76d9b6c9b5adac6c1b609afad7c6bcb5ddae6d715dcaee175abac5ccae5d71ab8b5b8adc16cab645a8ad3d68ab4359dace966ab34591ac8963ab1c584ac1d606b0157dabe95eaaf4565ab2958aac4561ab0957aabc55baad5562aaf54daa6952aa94530a97d4b6a59525a92948aa44519a8c945aa2c50ca85d426a11505a82940aa044eda7693aa9d44e9a74939a9cc4e3a7153829bf4d5a6a934a9a44b8a5bd2d696926f13749b64da26c135c9aa4d426993489a04cf250127893249724b1254924491248122c912484241120490047d23e11ec89844a222910c88444121f10f487843721a90c085c42d21610a48504271f20f8c7c43e11f00f7c5aa2d31690b405982cb1648b145882c015f0af45762b715b0ad05602af13809bc4d826b134099c3901c60e2870c37e1be0de06e036e1b30d886c035c1aa0d4869c3461a205c82e01620b005782b80a8053026811c052015
def ridgeSupport200_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport200_code
def ridgeSupport200_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport200_code
def ridgeSupport200_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport200_code
def ridgeSupport200_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport200_code
def ridgeSupport200_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport200_code
def ridgeSupport200_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport200_code
def ridgeSupport200_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport200_code
def ridgeSupport200_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport200_code
def ridgeSupport200_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport200_code
def ridgeSupport200_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport200_code
def ridgeSupport200_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport200_code
def ridgeSupport200_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport200_code
def ridgeSupport200_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport200_code
def ridgeSupport200_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport200_code
def ridgeSupport200_suffix_013 : List Nat := []
def ridgeSupport200_suffix_012 : List Nat := ridgeSupport200_012 ++ ridgeSupport200_suffix_013
def ridgeSupport200_suffix_011 : List Nat := ridgeSupport200_011 ++ ridgeSupport200_suffix_012
def ridgeSupport200_suffix_010 : List Nat := ridgeSupport200_010 ++ ridgeSupport200_suffix_011
def ridgeSupport200_suffix_009 : List Nat := ridgeSupport200_009 ++ ridgeSupport200_suffix_010
def ridgeSupport200_suffix_008 : List Nat := ridgeSupport200_008 ++ ridgeSupport200_suffix_009
def ridgeSupport200_suffix_007 : List Nat := ridgeSupport200_007 ++ ridgeSupport200_suffix_008
def ridgeSupport200_suffix_006 : List Nat := ridgeSupport200_006 ++ ridgeSupport200_suffix_007
def ridgeSupport200_suffix_005 : List Nat := ridgeSupport200_005 ++ ridgeSupport200_suffix_006
def ridgeSupport200_suffix_004 : List Nat := ridgeSupport200_004 ++ ridgeSupport200_suffix_005
def ridgeSupport200_suffix_003 : List Nat := ridgeSupport200_003 ++ ridgeSupport200_suffix_004
def ridgeSupport200_suffix_002 : List Nat := ridgeSupport200_002 ++ ridgeSupport200_suffix_003
def ridgeSupport200_suffix_001 : List Nat := ridgeSupport200_001 ++ ridgeSupport200_suffix_002
def ridgeSupport200_suffix_000 : List Nat := ridgeSupport200_000 ++ ridgeSupport200_suffix_001
theorem ridgeSupport200_source : candidateSupports 200 =
    (PackedRawNatGrowth.readList 13 404 ridgeSupport200_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
