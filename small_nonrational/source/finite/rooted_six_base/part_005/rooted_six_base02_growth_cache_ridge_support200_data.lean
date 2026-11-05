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
def ridgeSupport200_000 : List Nat := [21,41,71,77,83,84,174,175,176,177,184,185,418,419,423,425,426,430,432,433,435,439,440,444,446,447,451,453,454,456,615,616]
def ridgeSupport200_001 : List Nat := [619,620,623,624,687,688,692,694,695,699,701,702,704,708,709,713,715,716,720,722,723,725,991,992,993,994,995,996,1063,1064,1065,1068]
def ridgeSupport200_002 : List Nat := [1069,1070,1072,1077,1079,1084,1085,1086,1089,1090,1091,1093,1098,1100,1147,1148,1149,1152,1153,1154,1156,1161,1163,1168,1169,1170,1173,1174,1175,1177,1182,1184]
def ridgeSupport200_003 : List Nat := [1231,1232,1234,1235,1236,1237,1239,1240,1242,1243,1245,1246,2409,2411,2415,2417,2468,2469,2474,2475,2495,2497,2501,2503,2508,2509,2514,2515,2516,2517,2522,2523]
def ridgeSupport200_004 : List Nat := [2564,2565,2570,2571,2577,2579,2583,2585,2604,2605,2610,2611,2628,2629,2634,2635,2649,2651,2655,2657,2708,2709,2714,2715,2735,2737,2741,2743,2748,2749,2754,2755]
def ridgeSupport200_005 : List Nat := [2756,2757,2762,2763,2804,2805,2810,2811,2817,2819,2823,2825,2844,2845,2850,2851,2868,2869,2874,2875,2883,2885,2895,2897,2916,2917,2928,2929,2955,2957,2967,2969]
def ridgeSupport200_006 : List Nat := [2988,2989,3000,3001,3441,3443,3447,3449,3452,3453,3458,3459,3500,3501,3506,3507,3527,3529,3533,3535,3540,3541,3546,3547,3548,3549,3554,3555,3561,3563,3567,3569]
def ridgeSupport200_007 : List Nat := [3596,3597,3602,3603,3620,3621,3626,3627,3644,3645,3656,3657,4017,4019,4023,4025,4028,4029,4034,4035,4076,4077,4082,4083,4103,4105,4109,4111,4116,4117,4122,4123]
def ridgeSupport200_008 : List Nat := [4124,4125,4130,4131,4137,4139,4143,4145,4172,4173,4178,4179,4196,4197,4202,4203,4221,4223,4251,4253,4266,4267,4284,4285,4293,4295,4323,4325,4338,4339,4356,4357]
def ridgeSupport200_009 : List Nat := [4857,4859,4869,4871,4902,4903,4914,4915,4929,4931,4941,4943,4974,4975,4986,4987,5747,5749,5751,5753,5771,5773,5777,5779,5784,5785,5790,5791,5792,5793,5798,5799]
def ridgeSupport200_010 : List Nat := [5832,5833,5838,5839,5840,5841,5846,5847,5853,5855,5859,5861,5871,5872,5874,5875,5879,5881,5883,5885,5903,5905,5909,5911,5916,5917,5922,5923,5924,5925,5930,5931]
def ridgeSupport200_011 : List Nat := [5964,5965,5970,5971,5972,5973,5978,5979,5985,5987,5991,5993,6003,6004,6006,6007,6012,6013,6015,6017,6024,6025,6027,6029,6048,6049,6060,6061,6066,6067,6069,6071]
def ridgeSupport200_012 : List Nat := [6078,6079,6081,6083,6102,6103,6114,6115,6371,6373,6375,6377,6380,6381,6386,6387,6407,6409,6413,6415,6420,6421,6426,6427,6428,6429,6434,6435,6441,6443,6447,6449]
def ridgeSupport200_013 : List Nat := [6468,6469,6474,6475,6476,6477,6479,6480,6488,6489,6659,6661,6663,6665,6668,6669,6674,6675,6695,6697,6701,6703,6708,6709,6714,6715,6716,6717,6722,6723,6729,6731]
def ridgeSupport200_014 : List Nat := [6735,6737,6756,6757,6762,6763,6764,6765,6767,6768,6777,6779,6786,6787,6804,6805,6807,6809,6822,6823,6824,6826,6831,6833,6840,6841,6858,6859,6861,6863,6876,6877]
def ridgeSupport200_015 : List Nat := [6878,6880,7161,7163,7170,7171,7173,7175,7182,7183,7184,7186,7190,7192,7215,7217,7224,7225,7227,7229,7236,7237,7238,7240,7244,7246,7427,7429,7431,7433,7439,7441]
def ridgeSupport200_016 : List Nat := [7443,7445,7452,7453,7458,7459,7486,7488,7490,7492,7510,7512,7514,7516,7521,7523,7527,7529,7556,7558,7562,7564,7746,7747,7782,7783,7868,7869,7964,7965]
def ridgeSupport200_code : Nat := 0x3e3bf1cf5efaf3ccfe66f21f90bb19d8aec37613ad3d67eb1f587ab9d5aeac755ba89d42ea074fba47d22e8ef473a2bd13e88f43fa13d07e82f40f89dc4ce24711b88bc44e1ef0ef873c38e18f0bf831c16e09704381fc0ee03f017807c02dfdefe75c1aded6eeb7359facdd65eb2b573ab8d58eabf555aa8d53ea9b533a97d4aea53507a82d3de9e74e1a6fd36e9b34d7a6ad32e9934a3a4fd25e927487a42d1ee8f3477a3ad1ae8d345fa2dd14e89f427a12d06e833413a07d02e80f2b3958ca8653f29b94cca5e52b28b944c98e4bf257929c91e48b23b91cc8de46b22b914c87e437213907c79e3cb1db8ecc74e39f1cb8e3bf1df8afaf7d6be1df06f7f7bebdbded6f677b2bd6deb2f437a0bc6de2ef13788bc0ddfeefb77cbbbdddaee9773bb4dd9eec7761baddd6aeab754ba9dd4ae9b74cb95dcaae4b724b91dc8ae3b71cb8bdc56e2370fb7edbeedf36f7b79dbcade16efb72db8edbf6ddb6bdb5ada36d0b67db3ad936c8b53da9ad436a0b4fda7ad33698b49da46d1b68bb3cd9deceb6739bdcdea6df36e9a7cd36687341999ccca64f326983cc165f72f9882c4121e70f2872c38e18f0c585ec2f21570aa84ec26e0ff07d835c1aa0cb064829c14a09b04c818c0be057029811c08a03b01c80dc06a02b014807c0360130077f9bfc9fdafec7e1bf09f7afbc7dcbeddf66fb1724b921c7ae3c715b8a9c4ae24709b849c1ae0c6f8b7bdbd6de96f1b789bbaddc6edb769baadd46e7b735b92dc76d9b6c9b5adac6c1b609afad7c6bcb5ddae6d715dcaee175abac5ccae5d71ab8b5b8adc16cab645a8ad3d68ab4359dace966ab34591ac8963ab1c584ac1d606b0157dabe95eaaf4565ab2958aac4561ab0957aabc55baad5562aaf54daa6952aa94530a97d4b6a59525a92948aa44519a8c945aa2c50ca85d426a11505a82940aa044eda7693aa9d44e9a74939a9cc4e3a7153829bf4d5a6a934a9a44b8a5bd2d696926f13749b64da26c135c9aa4d426993489a04cf250127893249724b1254924491248122c912484241120490047d23e11ec89844a222910c88444121f10f487843721a90c085c42d21610a48504271f20f8c7c43e11f00f7c5aa2d31690b405982cb1648b145882c015f0af45762b715b0ad05602af13809bc4d826b134099c3901c60e2870c37e1be0de06e036e1b30d886c035c1aa0d4869c3461a205c82e01620b005782b80a8053026811c052015
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
def ridgeSupport200_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport200_code
def ridgeSupport200_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport200_code
def ridgeSupport200_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport200_code
def ridgeSupport200_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport200_code
def ridgeSupport200_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport200_code
def ridgeSupport200_suffix_017 : List Nat := []
def ridgeSupport200_suffix_016 : List Nat := ridgeSupport200_016 ++ ridgeSupport200_suffix_017
def ridgeSupport200_suffix_015 : List Nat := ridgeSupport200_015 ++ ridgeSupport200_suffix_016
def ridgeSupport200_suffix_014 : List Nat := ridgeSupport200_014 ++ ridgeSupport200_suffix_015
def ridgeSupport200_suffix_013 : List Nat := ridgeSupport200_013 ++ ridgeSupport200_suffix_014
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
    (PackedRawNatGrowth.readList 13 542 ridgeSupport200_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
