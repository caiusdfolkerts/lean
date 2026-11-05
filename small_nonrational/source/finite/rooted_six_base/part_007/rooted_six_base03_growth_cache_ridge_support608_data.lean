module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport608_000 : List Nat := [53,73,93,103,112,113,565,566,567,568,575,576,721,722,723,724,731,732,874,876,878,880,882,887,888,890,893,895,897,899,901,903]
def ridgeSupport608_001 : List Nat := [908,909,911,914,986,987,988,989,996,997,1139,1141,1143,1145,1147,1152,1153,1155,1158,1160,1162,1164,1166,1168,1173,1174,1176,1179,1251,1252,1253,1254]
def ridgeSupport608_002 : List Nat := [1261,1262,1404,1406,1408,1410,1412,1417,1418,1420,1423,1425,1427,1429,1431,1433,1438,1439,1441,1444,1513,1515,1517,1519,1521,1526,1527,1529,1532,1534,1536,1538]
def ridgeSupport608_003 : List Nat := [1540,1542,1547,1548,1550,1553,1602,1603,1605,1606,1609,1610,1611,1613,1614,1616,1623,1624,3006,3008,3015,3017,3030,3032,3038,3039,3044,3045,3051,3053,3058,3059]
def ridgeSupport608_004 : List Nat := [3072,3073,3086,3087,3092,3093,3106,3107,3108,3113,3114,3119,3120,3121,3129,3131,3132,3134,3138,3140,3147,3149,3162,3164,3170,3171,3176,3177,3183,3185,3190,3191]
def ridgeSupport608_005 : List Nat := [3204,3205,3218,3219,3224,3225,3238,3239,3240,3245,3246,3251,3252,3253,3261,3263,3264,3266,3326,3327,3330,3335,3338,3339,3342,3347,3362,3363,3374,3375,3380,3381]
def ridgeSupport608_006 : List Nat := [3384,3389,3392,3393,3396,3401,3416,3417,3428,3429,3486,3488,3495,3497,3510,3512,3518,3519,3524,3525,3531,3533,3538,3539,3552,3553,3566,3567,3572,3573,3586,3587]
def ridgeSupport608_007 : List Nat := [3588,3593,3594,3599,3600,3601,3609,3611,3612,3614,3674,3675,3678,3683,3686,3687,3690,3695,3710,3711,3722,3723,3728,3729,3732,3737,3740,3741,3744,3749,3764,3765]
def ridgeSupport608_008 : List Nat := [3776,3777,3834,3836,3843,3845,3858,3860,3866,3867,3872,3873,3879,3881,3886,3887,3900,3901,3914,3915,3920,3921,3934,3935,3936,3941,3942,3947,3948,3949,3957,3959]
def ridgeSupport608_009 : List Nat := [3960,3962,4022,4023,4026,4031,4034,4035,4038,4043,4058,4059,4070,4071,4076,4077,4080,4085,4088,4089,4092,4097,4112,4113,4124,4125,4238,4239,4242,4247,4250,4251]
def ridgeSupport608_010 : List Nat := [4254,4259,4274,4275,4286,4287,4292,4293,4296,4301,4304,4305,4308,4313,4328,4329,4340,4341,4530,4532,4539,4541,4542,4544,4551,4553,4562,4563,4568,4569,4578,4580]
def ridgeSupport608_011 : List Nat := [4587,4589,4598,4599,4604,4605,4614,4616,4623,4625,4634,4635,4640,4641,4658,4659,4664,4665,5028,5029,5064,5065,5124,5125,5184,5185]
def ridgeSupport608_code : Nat := 0x2883440a02d0127933c89d2ce92473238919c8ca44322090dc86a42320f904481a3fb1fc8fbc7da3db1eb8f2478a3b31d88e9c74a3931c78e046fa37b1bb8da46ca1eb0f4874c3a21b30d4868c34219b0c8862c31217f0be859c2ca14709e84dc26a12f092847c23a03b01c808c042002ffc7fcbfe1feaff07f6bfb1fcefe67edbf69f96fc67e1bf09f7efba7dbbed9ef4f787bbbdd5edaf6c7b5bd99ecaf607afbd79ea2f507a5bd29e7af3c797bcb9e52f27790bc81e36f1a78a3c49e0af0377e3be9d82ec075abad1d4aea074eba71d32e94748ba41d16e8a73fb9f9cdee6a733b999cc6e5e72db969c3ce1c70db865c22e10707b829c12e04701b809beadf46f7b7b9bc2de06e9b749b9adcb6e2b711b7edbe6dc36d9b52da76d03679acad646acb561a92d446a0b501a7ad3869ab4d1a5ed2e691b489a26d0e685b429a0ed0267fb3f9984cc065fb2f596acb4659b2b995aca8653b299932c98649b24990ac8463bb1d98e2c6f634b1a18c6c6262e316989ac4b622310987cc3c61db0e5862c30617b0a9852c24611b08982ac14607b039802c005f9afc97dabeb5f2af917bebde5ec2f59792bc75e02ef8cb06573281938c9a64b3251924c8c6453219908c2260e306182cc0c6043011800bfc5fc2fc97dcbec5f12f797b4bd65e92d21684b3e59e2cc965cb2a5932c8963cb1858a2c49610b045802bf15f09dc4ed27313949c84e324d926092c495248123891848a244121890648124011ec8f247723a91cc7ca3e41ee8f707b63da1c90e3c71a38c1c38e147063811bf8df46f43781bb8dc86e036e1b60da85b82db16a0b4c5a42d112008fc47023711b08d40e20700338174092035
def ridgeSupport608_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport608_code
def ridgeSupport608_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport608_code
def ridgeSupport608_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport608_code
def ridgeSupport608_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport608_code
def ridgeSupport608_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport608_code
def ridgeSupport608_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport608_code
def ridgeSupport608_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport608_code
def ridgeSupport608_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport608_code
def ridgeSupport608_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport608_code
def ridgeSupport608_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport608_code
def ridgeSupport608_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport608_code
def ridgeSupport608_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport608_code
def ridgeSupport608_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport608_code
def ridgeSupport608_suffix_012 : List Nat := []
def ridgeSupport608_suffix_011 : List Nat := ridgeSupport608_011 ++ ridgeSupport608_suffix_012
def ridgeSupport608_suffix_010 : List Nat := ridgeSupport608_010 ++ ridgeSupport608_suffix_011
def ridgeSupport608_suffix_009 : List Nat := ridgeSupport608_009 ++ ridgeSupport608_suffix_010
def ridgeSupport608_suffix_008 : List Nat := ridgeSupport608_008 ++ ridgeSupport608_suffix_009
def ridgeSupport608_suffix_007 : List Nat := ridgeSupport608_007 ++ ridgeSupport608_suffix_008
def ridgeSupport608_suffix_006 : List Nat := ridgeSupport608_006 ++ ridgeSupport608_suffix_007
def ridgeSupport608_suffix_005 : List Nat := ridgeSupport608_005 ++ ridgeSupport608_suffix_006
def ridgeSupport608_suffix_004 : List Nat := ridgeSupport608_004 ++ ridgeSupport608_suffix_005
def ridgeSupport608_suffix_003 : List Nat := ridgeSupport608_003 ++ ridgeSupport608_suffix_004
def ridgeSupport608_suffix_002 : List Nat := ridgeSupport608_002 ++ ridgeSupport608_suffix_003
def ridgeSupport608_suffix_001 : List Nat := ridgeSupport608_001 ++ ridgeSupport608_suffix_002
def ridgeSupport608_suffix_000 : List Nat := ridgeSupport608_000 ++ ridgeSupport608_suffix_001
theorem ridgeSupport608_source : candidateSupports 608 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport608_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
