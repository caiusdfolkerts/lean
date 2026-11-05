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
def ridgeSupport400_000 : List Nat := [60,74,90,93,96,881,882,883,886,887,892,893,898,900,943,944,948,950,951,955,957,958,960,1025,1026,1029,1030,1033,1034,1062,1063,1064]
def ridgeSupport400_001 : List Nat := [1067,1068,1073,1074,1079,1081,1124,1125,1129,1131,1132,1136,1138,1139,1141,1254,1258,1259,1260,1261,1263,1264,1271,1273,1319,1320,1321,1324,1325,1326,1328,1333]
def ridgeSupport400_002 : List Nat := [1335,1338,1341,1342,1343,1346,1347,1348,1350,1355,1356,1358,1359,3165,3167,3184,3186,3244,3245,3250,3251,3264,3265,3267,3270,3273,3276,3278,3279,3292,3293,3298]
def ridgeSupport400_003 : List Nat := [3299,3333,3335,3340,3341,3346,3347,3352,3354,3360,3361,3374,3375,3384,3385,3398,3399,3405,3407,3424,3426,3484,3485,3490,3491,3504,3505,3507,3510,3513,3516,3518]
def ridgeSupport400_004 : List Nat := [3519,3532,3533,3538,3539,3573,3575,3580,3581,3586,3587,3592,3594,3600,3601,3614,3615,3624,3625,3638,3639,3696,3697,3700,3701,4533,4535,4552,4554,4564,4565,4570]
def ridgeSupport400_005 : List Nat := [4571,4612,4613,4618,4619,4632,4633,4635,4638,4641,4644,4646,4647,4653,4655,4660,4661,4666,4667,4672,4674,4708,4709,4714,4715,4732,4733,4738,4739,4800,4801,4808]
def ridgeSupport400_006 : List Nat := [4809,4846,4848,4876,4878,4886,4887,4904,4905,5061,5063,5091,5093,5106,5107,5124,5125,6225,6227,6232,6234,6252,6253,6255,6258,6261,6264,6266,6267,6280,6281,6286]
def ridgeSupport400_007 : List Nat := [6287,6300,6301,6314,6315,6321,6323,6328,6329,6334,6335,6340,6342,6345,6346,6353,6354,6357,6359,6364,6366,6384,6385,6387,6390,6393,6396,6398,6399,6412,6413,6418]
def ridgeSupport400_008 : List Nat := [6419,6432,6433,6446,6447,6453,6455,6460,6461,6466,6467,6472,6474,6477,6478,6485,6486,6502,6503,7005,7007,7012,7014,7024,7025,7030,7031,7044,7045,7047,7050,7053]
def ridgeSupport400_009 : List Nat := [7056,7058,7059,7065,7067,7072,7073,7078,7079,7084,7086,7092,7093,7106,7107,7115,7117,7118,7120,7138,7139,7150,7152,7154,7155,7172,7173,7180,7182,7190,7191,7199]
def ridgeSupport400_010 : List Nat := [7201,7311,7313,7320,7321,7338,7339,7341,7343,7356,7357,7358,7360,7473,7475,7480,7482,7485,7487,7492,7494,7544,7546,7553,7555,7558,7560,7575,7577,7836,7837,7872]
def ridgeSupport400_011 : List Nat := [7873,8030,8031]
def ridgeSupport400_code : Nat := 0x7d7febdec1f607a77d39d99ecbf623b0dd83ec0f5ebaf1d46ea274ffa7bd3ae9c74cfa63cc0e5f72f7979cafe56f2af955c99e4c724791fc21e0ff05f82dc0ee067017809bf3df96fc37ddbe3df16f4379dbcdde5ef0f785bb5dda6ebb759ba7dd36e87741b9bdccee4f725b90dc6ee2b70fb85dc26ddf6edb71db86d9b6c9b5fdaee59f2cd956caae53b29b94aca4650f28593dc9e64df26b92fc976487241913c8964372198ffc7f63f31f38f6c79e3c71e18dec6e635f1ab8d2c68e32b1938c6c6262ff17d8b9c5c62cf1638abc55627713988fc47622711187bc3d61e30eb872c37e1b70d985ac2c614f0a3405a024fce7e53e59f1cf1e78b3299944c5e62d30e9864bc25dd2c99644b0658128394149f64f926b93549964c924292048ee47523591a48be45b227913489244321e90dc86643120b90548164091db8ed47563a91ca8e446de36ae7573a39c5ce0e3771b38a5c50e1f70f3845c20e0a704380dc04dfd6fe37ddbeadd36e93735b98dbf6df36f1b72db66d9b6c5b60da36d13675b38d626b0353da9ad476a334e5a70d2f6973485a40d1a68c344da24d0d686341da0ace367133759b8ccf6673331992cc6661b305980cb365932b5958c72638317d8ba54f2a71530a965462a2150ca8453f29f14f4a7453729a94c0a5c52d29614a4a5052727c93dc9e04ef27693b09d64ea27311d48e647223811b08d6469232919087243721910c485842b214109c84c40a204901880a4022008f0077c3bd1dd8edc76c3b41d80ebc7083821be8df06ee3761b98dc86e206002e816809403c
def ridgeSupport400_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport400_code
def ridgeSupport400_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport400_code
def ridgeSupport400_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport400_code
def ridgeSupport400_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport400_code
def ridgeSupport400_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport400_code
def ridgeSupport400_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport400_code
def ridgeSupport400_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport400_code
def ridgeSupport400_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport400_code
def ridgeSupport400_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport400_code
def ridgeSupport400_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport400_code
def ridgeSupport400_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport400_code
def ridgeSupport400_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport400_code
def ridgeSupport400_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport400_code
def ridgeSupport400_suffix_012 : List Nat := []
def ridgeSupport400_suffix_011 : List Nat := ridgeSupport400_011 ++ ridgeSupport400_suffix_012
def ridgeSupport400_suffix_010 : List Nat := ridgeSupport400_010 ++ ridgeSupport400_suffix_011
def ridgeSupport400_suffix_009 : List Nat := ridgeSupport400_009 ++ ridgeSupport400_suffix_010
def ridgeSupport400_suffix_008 : List Nat := ridgeSupport400_008 ++ ridgeSupport400_suffix_009
def ridgeSupport400_suffix_007 : List Nat := ridgeSupport400_007 ++ ridgeSupport400_suffix_008
def ridgeSupport400_suffix_006 : List Nat := ridgeSupport400_006 ++ ridgeSupport400_suffix_007
def ridgeSupport400_suffix_005 : List Nat := ridgeSupport400_005 ++ ridgeSupport400_suffix_006
def ridgeSupport400_suffix_004 : List Nat := ridgeSupport400_004 ++ ridgeSupport400_suffix_005
def ridgeSupport400_suffix_003 : List Nat := ridgeSupport400_003 ++ ridgeSupport400_suffix_004
def ridgeSupport400_suffix_002 : List Nat := ridgeSupport400_002 ++ ridgeSupport400_suffix_003
def ridgeSupport400_suffix_001 : List Nat := ridgeSupport400_001 ++ ridgeSupport400_suffix_002
def ridgeSupport400_suffix_000 : List Nat := ridgeSupport400_000 ++ ridgeSupport400_suffix_001
theorem ridgeSupport400_source : candidateSupports 400 =
    (PackedRawNatGrowth.readList 13 355 ridgeSupport400_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
