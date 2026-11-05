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
def ridgeSupport290_000 : List Nat := [39,48,50,52,529,627,630,631,634,637,651,654,655,658,661,676,677,680,681,686,771,772,774,775,778,779,780,782,783,785,790,791]
def ridgeSupport290_001 : List Nat := [813,815,816,818,819,821,823,824,826,827,830,831,834,836,837,839,840,842,844,845,847,848,851,852,3742,3743,3748,3749,3752,3753,3754,3755]
def ridgeSupport290_002 : List Nat := [3756,3757,3762,3763,3766,3767,3772,3773,3776,3777,3778,3779,3780,3781,3786,3787,3800,3801,3802,3803,3804,3805,3824,3825,3826,3827,3828,3829,3848,3849,3850,3851]
def ridgeSupport290_003 : List Nat := [3852,3853,3872,3873,3874,3875,3876,3877,3896,3897,3898,3899,3900,3901,3920,3921,3922,3923,3924,3925,3933,3936,3939,3942,3944,3945,3946,3947,3948,3949,3950,3952]
def ridgeSupport290_004 : List Nat := [4230,4231,4248,4249,4266,4267,4268,4270,4274,4276,4284,4285,4372,4373,4390,4391,4408,4409,4413,4416,4419,4422,4426,4427,4444,4445,4462,4463,4480,4481,4485,4488]
def ridgeSupport290_005 : List Nat := [4491,4494,4498,4499,4765,4767,4770,4772,4777,4779,4797,4799,4802,4804,4809,4811,4828,4830,4835,4837,4840,4842,6514,6515,6518,6519,6522,6523,6526,6527,6530,6531]
def ridgeSupport290_006 : List Nat := [6534,6535,6548,6549,6550,6551,6552,6553,6572,6573,6574,6575,6576,6577,6585,6588,6591,6594,6596,6597,6598,6599,6600,6601,6602,6604,6609,6612,6615,6618,6620,6621]
def ridgeSupport290_007 : List Nat := [6622,6623,6624,6625,6626,6628,6632,6634,6635,6637,6642,6643,6786,6787,6788,6790,6794,6796,6804,6805,6813,6815,6822,6823,6824,6826,6892,6893,6897,6900,6903,6906]
def ridgeSupport290_008 : List Nat := [6910,6911,6920,6925,6928,6929,6933,6936,6946,6947,6951,6954,6957,6960,6964,6965,6974,6979,6982,6983,6987,6990,7129,7130,7137,7138,7144,7147,7498,7499,7502,7503]
def ridgeSupport290_009 : List Nat := [7506,7507,7521,7523,7532,7537,7538,7543,7916,7917,7918,7919,7920,7921,8043,8051,8058]
def ridgeSupport290_code : Nat := 0x1f7afb9fdafde3ef0f77fbbbddbeecebbf5cbae3d6ceb1f587aa7d52ea7f53ba97d4adf5efa37c5be1ded6f6769db4bda3ed1b687b3ed9aecd3661b2dd956c9f647b22d8c6c57623b10d86ec235ffafed7d6bdf5e9af1d76ebb3555aa8d53ea9b53fa9dd4aea53519a8ad436a13507a82cf9e7cb3db9ebcf567a33c99e2cf0e7833bf9deceee7733b59d7cea67473999cace4e72338f9c6ce2e7133859bfcde66e73639b0cd7e6bb35b9acccce66332f996ccae65330f986cc1e60b2ff97ecbde5eb2ef976cb9e5ca5d52e8972cb8e5bd2dc965cb265892c295fcaf65572a99524a8a53f29d8c9c64a31d18b8c446163031808b7c5ba2bb15c8a5c52a28d1438a044f6273138893c49a22b11485ec2f21690b285742b21570aa84cc26210f0867b83db9edaf6c7b5bda9ed2f687b33d8dec0f5d7aabd51ea6f527a8bd41e7af3c79dbce9e72f38792bc91e46f22790bc81e1af0c785bc29e12f0877abbd1de6ef2778bbc1dbaedc76dbb69db2ed8765bb29d8aec4761bb09d82ec075ebaf1d6eeb6759bac9d5aeac755baa9d52ea8752ba91d3ee9e1aa0d4c6a034f1a68d306943481a38d1468834219f8cf867633a19c0cdc66a3331990cc065e32d18b8c5862230f1870c3061630a1838c186083031570aa45502a51520a5452428f1470a2c4fa27a13b89d84e621101a00c8060027
def ridgeSupport290_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport290_code
def ridgeSupport290_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport290_code
def ridgeSupport290_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport290_code
def ridgeSupport290_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport290_code
def ridgeSupport290_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport290_code
def ridgeSupport290_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport290_code
def ridgeSupport290_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport290_code
def ridgeSupport290_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport290_code
def ridgeSupport290_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport290_code
def ridgeSupport290_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport290_code
def ridgeSupport290_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport290_code
def ridgeSupport290_suffix_010 : List Nat := []
def ridgeSupport290_suffix_009 : List Nat := ridgeSupport290_009 ++ ridgeSupport290_suffix_010
def ridgeSupport290_suffix_008 : List Nat := ridgeSupport290_008 ++ ridgeSupport290_suffix_009
def ridgeSupport290_suffix_007 : List Nat := ridgeSupport290_007 ++ ridgeSupport290_suffix_008
def ridgeSupport290_suffix_006 : List Nat := ridgeSupport290_006 ++ ridgeSupport290_suffix_007
def ridgeSupport290_suffix_005 : List Nat := ridgeSupport290_005 ++ ridgeSupport290_suffix_006
def ridgeSupport290_suffix_004 : List Nat := ridgeSupport290_004 ++ ridgeSupport290_suffix_005
def ridgeSupport290_suffix_003 : List Nat := ridgeSupport290_003 ++ ridgeSupport290_suffix_004
def ridgeSupport290_suffix_002 : List Nat := ridgeSupport290_002 ++ ridgeSupport290_suffix_003
def ridgeSupport290_suffix_001 : List Nat := ridgeSupport290_001 ++ ridgeSupport290_suffix_002
def ridgeSupport290_suffix_000 : List Nat := ridgeSupport290_000 ++ ridgeSupport290_suffix_001
theorem ridgeSupport290_source : candidateSupports 290 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport290_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
