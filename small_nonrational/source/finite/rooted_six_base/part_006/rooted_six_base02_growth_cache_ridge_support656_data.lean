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
def ridgeSupport656_000 : List Nat := [61,75,91,94,96,902,903,904,907,908,913,914,919,921,943,945,947,949,951,956,957,959,962,1037,1038,1041,1042,1045,1046,1083,1084,1085]
def ridgeSupport656_001 : List Nat := [1088,1089,1094,1095,1100,1102,1124,1126,1128,1130,1132,1137,1138,1140,1143,1275,1279,1280,1281,1282,1284,1285,1292,1294,1318,1320,1322,1323,1325,1327,1328,1332]
def ridgeSupport656_002 : List Nat := [1337,1338,1340,1342,1344,1345,1347,1349,1350,1354,1356,1361,1362,3164,3169,3178,3180,3246,3247,3256,3257,3262,3263,3266,3268,3272,3273,3279,3282,3294,3295,3304]
def ridgeSupport656_003 : List Nat := [3305,3332,3337,3342,3343,3346,3348,3352,3353,3358,3359,3368,3369,3382,3383,3392,3393,3404,3409,3418,3420,3486,3487,3496,3497,3502,3503,3506,3508,3512,3513,3519]
def ridgeSupport656_004 : List Nat := [3522,3534,3535,3544,3545,3572,3577,3582,3583,3586,3588,3592,3593,3598,3599,3608,3609,3622,3623,3632,3633,3712,3713,3716,3717,4532,4537,4546,4548,4566,4567,4576]
def ridgeSupport656_005 : List Nat := [4577,4614,4615,4624,4625,4630,4631,4634,4636,4640,4641,4647,4650,4652,4657,4662,4663,4666,4668,4672,4673,4710,4711,4720,4721,4734,4735,4744,4745,4816,4817,4824]
def ridgeSupport656_006 : List Nat := [4825,4918,4920,4948,4950,4958,4959,4976,4977,5060,5065,5090,5095,5104,5105,5122,5123,6224,6229,6230,6234,6250,6251,6254,6256,6260,6261,6267,6270,6282,6283,6292]
def ridgeSupport656_007 : List Nat := [6293,6298,6299,6308,6309,6320,6325,6330,6331,6334,6336,6340,6341,6344,6346,6350,6351,6356,6361,6362,6366,6382,6383,6386,6388,6392,6393,6399,6402,6414,6415,6424]
def ridgeSupport656_008 : List Nat := [6425,6430,6431,6440,6441,6452,6457,6462,6463,6466,6468,6472,6473,6476,6478,6482,6483,6506,6507,7004,7009,7010,7014,7026,7027,7036,7037,7042,7043,7046,7048,7052]
def ridgeSupport656_009 : List Nat := [7053,7059,7062,7064,7069,7074,7075,7078,7080,7084,7085,7090,7091,7100,7101,7116,7117,7121,7123,7142,7143,7204,7206,7208,7209,7226,7227,7234,7236,7244,7245,7253]
def ridgeSupport656_010 : List Nat := [7255,7310,7315,7318,7319,7336,7337,7340,7345,7354,7355,7359,7362,7472,7477,7478,7482,7484,7489,7490,7494,7545,7548,7551,7555,7564,7566,7574,7579,7834,7835,7870]
def ridgeSupport656_011 : List Nat := [7871,8032,8033]
def ridgeSupport656_code : Nat := 0x7d87ec1ebff5f7a6fd35d9becb763bb19d83ebff5f3af3d46ea17507a79d3ae9b74d7a61cc2e5ff2ef975cb1e5672a7951c97e4b724f91dc57e2af137899c44e2170ef875c29e14709b849be7df36f4f7a3bcdde66ef7779bb3dd96eb7759ba8dd36e8f745b9ddcc6e5b727b8ddc66e2370db83dc16df76f9b73db96d9b6c5b61dae65af2d5953ca9653b299949ca4651328593fc9f64e7269929c94647f23d919c8c643f21d902c7fe3e71f18f4c7963bf1dd8dec6d63671a98cfc67632b1918c5c62630317d8bbc5d62d71618a5c52626f135895c4a622f11587ec3de1d70e9870c3761af0d585ac2b61570a1403a014fc67e13e79f14f267893719b84d7e6bd3569aa4ce266d2d996c4b465a128994449fe4fd271938499e4cd24192048f247523791b48c645922a913c88644121c90d485e42d211908481e40d1e18f0475e3ad1c48e146e6368e857423a05d00e31718389dc4ce1970c383dc1ce097043811c04dff6ff37e5be8dd96ec373db9cdc26dfb6e5b70db46d936bdb5cda96d4367db3cd5c6ad3545a98d416a034dda6cd29694347da3cd1968c3451a24d0f6873425a08ce9674337d9bccd2667b325990cc466132fd97ccb965c32bd95cc6c63531858b85522a89530a945462a2950ca8254029f14f0a7453929a14c0a5e52d29594a8a505262871430a0a5042811404a004ff27d91dc8e847223891b08d4468233119089c44c223911888244021e90f087641620a904882240e2068f0877e3bd1de0edc76a3b31d88ebc7323971c90e4471838b1c40e1c70c06002f016c09603d
def ridgeSupport656_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport656_code
def ridgeSupport656_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport656_code
def ridgeSupport656_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport656_code
def ridgeSupport656_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport656_code
def ridgeSupport656_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport656_code
def ridgeSupport656_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport656_code
def ridgeSupport656_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport656_code
def ridgeSupport656_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport656_code
def ridgeSupport656_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport656_code
def ridgeSupport656_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport656_code
def ridgeSupport656_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport656_code
def ridgeSupport656_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport656_code
def ridgeSupport656_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport656_code
def ridgeSupport656_suffix_012 : List Nat := []
def ridgeSupport656_suffix_011 : List Nat := ridgeSupport656_011 ++ ridgeSupport656_suffix_012
def ridgeSupport656_suffix_010 : List Nat := ridgeSupport656_010 ++ ridgeSupport656_suffix_011
def ridgeSupport656_suffix_009 : List Nat := ridgeSupport656_009 ++ ridgeSupport656_suffix_010
def ridgeSupport656_suffix_008 : List Nat := ridgeSupport656_008 ++ ridgeSupport656_suffix_009
def ridgeSupport656_suffix_007 : List Nat := ridgeSupport656_007 ++ ridgeSupport656_suffix_008
def ridgeSupport656_suffix_006 : List Nat := ridgeSupport656_006 ++ ridgeSupport656_suffix_007
def ridgeSupport656_suffix_005 : List Nat := ridgeSupport656_005 ++ ridgeSupport656_suffix_006
def ridgeSupport656_suffix_004 : List Nat := ridgeSupport656_004 ++ ridgeSupport656_suffix_005
def ridgeSupport656_suffix_003 : List Nat := ridgeSupport656_003 ++ ridgeSupport656_suffix_004
def ridgeSupport656_suffix_002 : List Nat := ridgeSupport656_002 ++ ridgeSupport656_suffix_003
def ridgeSupport656_suffix_001 : List Nat := ridgeSupport656_001 ++ ridgeSupport656_suffix_002
def ridgeSupport656_suffix_000 : List Nat := ridgeSupport656_000 ++ ridgeSupport656_suffix_001
theorem ridgeSupport656_source : candidateSupports 656 =
    (PackedRawNatGrowth.readList 13 355 ridgeSupport656_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
