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
def ridgeSupport400_000 : List Nat := [60,74,90,93,96,881,882,883,886,887,892,893,898,900,943,944,948,950,951,955,957,958,960,1025,1026,1029,1030,1033,1034,1062,1063,1064]
def ridgeSupport400_001 : List Nat := [1067,1068,1073,1074,1079,1081,1124,1125,1129,1131,1132,1136,1138,1139,1141,1254,1258,1259,1260,1261,1263,1264,1271,1273,1319,1320,1321,1324,1325,1326,1328,1333]
def ridgeSupport400_002 : List Nat := [1335,1338,1341,1342,1343,1346,1347,1348,1350,1355,1356,1358,1359,3165,3167,3184,3186,3244,3245,3250,3251,3264,3265,3267,3270,3273,3276,3278,3279,3292,3293,3298]
def ridgeSupport400_003 : List Nat := [3299,3333,3335,3340,3341,3346,3347,3352,3354,3360,3361,3374,3375,3384,3385,3398,3399,3405,3407,3424,3426,3484,3485,3490,3491,3504,3505,3507,3510,3513,3516,3518]
def ridgeSupport400_004 : List Nat := [3519,3532,3533,3538,3539,3573,3575,3580,3581,3586,3587,3592,3594,3600,3601,3614,3615,3624,3625,3638,3639,3696,3697,3700,3701,4533,4535,4552,4554,4564,4565,4570]
def ridgeSupport400_005 : List Nat := [4571,4612,4613,4618,4619,4632,4633,4635,4638,4641,4644,4646,4647,4653,4655,4660,4661,4666,4667,4672,4674,4708,4709,4714,4715,4732,4733,4738,4739,4800,4801,4808]
def ridgeSupport400_006 : List Nat := [4809,4846,4848,4876,4878,4886,4887,4904,4905,5061,5063,5091,5093,5106,5107,5124,5125,5241,5243,5248,5250,5253,5255,5260,5262,5312,5314,5321,5323,5326,5328,5343]
def ridgeSupport400_007 : List Nat := [5345,5604,5605,5640,5641,5798,5799,6244,6245,6250,6251,6260,6262,6264,6265,6268,6271,6292,6293,6298,6299,6308,6310,6312,6313,6316,6319,6507,6510,6513,6516,6536]
def ridgeSupport400_008 : List Nat := [6538,6540,6541,6544,6547,6554,6555,6557,6559,6608,6610,6612,6613]
def ridgeSupport400_code : Nat := 0x19d5cea674b3a199fccee66f335993cc8663731998acc465d32e396ecb5e2bf1598a9c54629b14989bc4d625712987fc3e61e70f1876c3a61af0d5865c325a9ed4d609b045796bc94e1a6fd34299d4cba64d30a98148ea46521e90b482a4051ee8f3405a024fce7e53e59f1cf1e78b3299944c5e62d30e9864bc25dd2c99644b0658128394149f64f926b93549964c924292048ee47523591a48be45b227913489244321e90dc86643120b90548164091db8ed47563a91ca8e446de36ae7573a39c5ce0e3771b38a5c50e1f70f3845c20e0a704380dc04dfd6fe37ddbeadd36e93735b98dbf6df36f1b72db66d9b6c5b60da36d13675b38d626b0353da9ad476a334e5a70d2f6973485a40d1a68c344da24d0d686341da0ace367133759b8ccf6673331992cc6661b305980cb365932b5958c72638317d8ba54f2a71530a965462a2150ca8453f29f14f4a7453729a94c0a5c52d29614a4a5052727c93dc9e04ef27693b09d64ea27311d48e647223811b08d6469232919087243721910c485842b214109c84c40a204901880a4022008f0077c3bd1dd8edc76c3b41d80ebc7083821be8df06ee3761b98dc86e206002e816809403c
def ridgeSupport400_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport400_code
def ridgeSupport400_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport400_code
def ridgeSupport400_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport400_code
def ridgeSupport400_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport400_code
def ridgeSupport400_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport400_code
def ridgeSupport400_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport400_code
def ridgeSupport400_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport400_code
def ridgeSupport400_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport400_code
def ridgeSupport400_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport400_code
def ridgeSupport400_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport400_code
def ridgeSupport400_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 269 ridgeSupport400_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
