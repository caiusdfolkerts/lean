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
def ridgeSupport656_000 : List Nat := [61,75,91,94,96,902,903,904,907,908,913,914,919,921,943,945,947,949,951,956,957,959,962,1037,1038,1041,1042,1045,1046,1083,1084,1085]
def ridgeSupport656_001 : List Nat := [1088,1089,1094,1095,1100,1102,1124,1126,1128,1130,1132,1137,1138,1140,1143,1275,1279,1280,1281,1282,1284,1285,1292,1294,1318,1320,1322,1323,1325,1327,1328,1332]
def ridgeSupport656_002 : List Nat := [1337,1338,1340,1342,1344,1345,1347,1349,1350,1354,1356,1361,1362,3164,3169,3178,3180,3246,3247,3256,3257,3262,3263,3266,3268,3272,3273,3279,3282,3294,3295,3304]
def ridgeSupport656_003 : List Nat := [3305,3332,3337,3342,3343,3346,3348,3352,3353,3358,3359,3368,3369,3382,3383,3392,3393,3404,3409,3418,3420,3486,3487,3496,3497,3502,3503,3506,3508,3512,3513,3519]
def ridgeSupport656_004 : List Nat := [3522,3534,3535,3544,3545,3572,3577,3582,3583,3586,3588,3592,3593,3598,3599,3608,3609,3622,3623,3632,3633,3712,3713,3716,3717,4532,4537,4546,4548,4566,4567,4576]
def ridgeSupport656_005 : List Nat := [4577,4614,4615,4624,4625,4630,4631,4634,4636,4640,4641,4647,4650,4652,4657,4662,4663,4666,4668,4672,4673,4710,4711,4720,4721,4734,4735,4744,4745,4816,4817,4824]
def ridgeSupport656_006 : List Nat := [4825,4918,4920,4948,4950,4958,4959,4976,4977,5060,5065,5090,5095,5104,5105,5122,5123,5240,5245,5246,5250,5252,5257,5258,5262,5313,5316,5319,5323,5332,5334,5342]
def ridgeSupport656_007 : List Nat := [5347,5602,5603,5638,5639,5800,5801,6246,6247,6256,6257,6261,6262,6263,6264,6269,6270,6294,6295,6304,6305,6309,6310,6311,6312,6317,6318,6506,6508,6519,6522,6537]
def ridgeSupport656_008 : List Nat := [6538,6539,6540,6545,6546,6572,6573,6575,6577,6609,6610,6611,6612]
def ridgeSupport656_code : Nat := 0x19d4ce9e74b3a39b1cd7e6b7359992cc8e63331798acc4e5eb2ef96ccb562bb15b8a8c53e29b14b8a1c50625f12d87ec3ee1e30ef876c3ae1c70e1867c335aa6d51607b03578ebc54e3a6f535a9a94cba63d31298348ea455226909482a3f51f68f1403a014fc67e13e79f14f267893719b84d7e6bd3569aa4ce266d2d996c4b465a128994449fe4fd271938499e4cd24192048f247523791b48c645922a913c88644121c90d485e42d211908481e40d1e18f0475e3ad1c48e146e6368e857423a05d00e31718389dc4ce1970c383dc1ce097043811c04dff6ff37e5be8dd96ec373db9cdc26dfb6e5b70db46d936bdb5cda96d4367db3cd5c6ad3545a98d416a034dda6cd29694347da3cd1968c3451a24d0f6873425a08ce9674337d9bccd2667b325990cc466132fd97ccb965c32bd95cc6c63531858b85522a89530a945462a2950ca8254029f14f0a7453929a14c0a5e52d29594a8a505262871430a0a5042811404a004ff27d91dc8e847223891b08d4468233119089c44c223911888244021e90f087641620a904882240e2068f0877e3bd1de0edc76a3b31d88ebc7323971c90e4471838b1c40e1c70c06002f016c09603d
def ridgeSupport656_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport656_code
def ridgeSupport656_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport656_code
def ridgeSupport656_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport656_code
def ridgeSupport656_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport656_code
def ridgeSupport656_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport656_code
def ridgeSupport656_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport656_code
def ridgeSupport656_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport656_code
def ridgeSupport656_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport656_code
def ridgeSupport656_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport656_code
def ridgeSupport656_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport656_code
def ridgeSupport656_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 269 ridgeSupport656_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
