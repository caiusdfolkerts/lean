module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport864_000 : List Nat := [1325,1326,1327,1434,1435,1436,1543,1544,1545,1617,1618,1619,5472,5473,5474,5475,5476,5477,5568,5569,5570,5571,5572,5573,5664,5665,5666,5667,5668,5669,5736,5737]
def ridgeSupport864_001 : List Nat := [5738,5739,5740,5741,5832,5833,5834,5835,5836,5837,5928,5929,5930,5931,5932,5933,6216,6217,6218,6219,6220,6221,6228,6229,6230,6231,6232,6233,6432,6433,6434,6435]
def ridgeSupport864_002 : List Nat := [6436,6437,6528,6529,6530,6531,6532,6533,6624,6625,6626,6627,6628,6629,6912,6913,6914,6915,6916,6917,6924,6925,6926,6927,6928,6929,10242,10243,10256,10257,10262,10263]
def ridgeSupport864_003 : List Nat := [10269,10271,10279,10282,10285,10288,10290,10291,10304,10305,10310,10311,10389,10391,10399,10402,10405,10408,10437,10439,10447,10450,10453,10456,10482,10483,10496,10497,10502,10503,10509,10511]
def ridgeSupport864_004 : List Nat := [10519,10522,10525,10528,10530,10531,10544,10545,10550,10551,10629,10631,10639,10642,10645,10648,10677,10679,10687,10690,10693,10696,10908,10909,10910,10911,10912,10913,10920,10921,10922,10923]
def ridgeSupport864_005 : List Nat := [10924,10925,11010,11011,11024,11025,11030,11031,11037,11039,11047,11050,11053,11056,11058,11059,11072,11073,11078,11079,11157,11159,11167,11170,11173,11176,11205,11207,11215,11218,11221,11224]
def ridgeSupport864_006 : List Nat := [11436,11437,11438,11439,11440,11441,11448,11449,11450,11451,11452,11453,13569,13571,13576,13629,13631,13639,13642,13645,13648,13701,13703,13708,13761,13763,13771,13774,13777,13780,13968,13969]
def ridgeSupport864_007 : List Nat := [13970,13971,13972,13973,14049,14051,14056,14109,14111,14119,14122,14125,14128,14316,14317,14318,14319,14320,14321,15066,15067,15080,15081,15086,15087,15102,15103,15116,15117,15122,15123,15162]
def ridgeSupport864_008 : List Nat := [15163,15176,15177,15182,15183]
def ridgeSupport864_code : Nat := 0x3b4fed3bb49ed23b3becebb13ec4bb0dec33affebfbaefebbbae9eba3adbeb6b7f1dfc37efdfbb7eddfb3730dcb772adc9f71fdc776e8db8f6e1da57694da4f692da47690d7535d1d73b5cbd70f5c1d633587d617550d53754ad51f53fd4f7508d40f501b2f6cbcb2eecbab2e6cb8b2c6cb0b2becaeb2b6cacaf62bd5af4abcfaf1ebc5aea2ba5ae8ab9fae5eb95ad1eb46ad06b40acceb32acc2b2dacaab27ac7eb1dac5eb16ac46b10ac0eb02aab6aacaaaeaaaaaa6aa8aa86aa0aa7ea9eaa76a9ca7229c5a70a9bfa6de9b5a662995a64a98fa61e985a4de936a4c6930a48e922a48291da46a917a43e90da41e906a406900a3ce8f2a3628d5a34a8cfa31e8c5a2a28a5a28a89fa25e895a11e846a106840a0ce832a0c282da0aa827a07e81da05e816a046810a00e8026c45b106c3db0e6c35b0c6c15b046c0db026c05b0067959e4678d9e267859e06615984660d98266059806495924648d92264859206165858615d8566155854613584c612d84a61258485cb572c5cad72a5ca57285b356cc5b2d6ca5b256c859b566c59ad66a59a56685895624588d622588562057155c4570d5c257055c05595564558d5625585560194c65219446091820607167059b166852f14b852d
def ridgeSupport864_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport864_code
def ridgeSupport864_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport864_code
def ridgeSupport864_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport864_code
def ridgeSupport864_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport864_code
def ridgeSupport864_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport864_code
def ridgeSupport864_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport864_code
def ridgeSupport864_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport864_code
def ridgeSupport864_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport864_code
def ridgeSupport864_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport864_code
def ridgeSupport864_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport864_code
def ridgeSupport864_suffix_009 : List Nat := []
def ridgeSupport864_suffix_008 : List Nat := ridgeSupport864_008 ++ ridgeSupport864_suffix_009
def ridgeSupport864_suffix_007 : List Nat := ridgeSupport864_007 ++ ridgeSupport864_suffix_008
def ridgeSupport864_suffix_006 : List Nat := ridgeSupport864_006 ++ ridgeSupport864_suffix_007
def ridgeSupport864_suffix_005 : List Nat := ridgeSupport864_005 ++ ridgeSupport864_suffix_006
def ridgeSupport864_suffix_004 : List Nat := ridgeSupport864_004 ++ ridgeSupport864_suffix_005
def ridgeSupport864_suffix_003 : List Nat := ridgeSupport864_003 ++ ridgeSupport864_suffix_004
def ridgeSupport864_suffix_002 : List Nat := ridgeSupport864_002 ++ ridgeSupport864_suffix_003
def ridgeSupport864_suffix_001 : List Nat := ridgeSupport864_001 ++ ridgeSupport864_suffix_002
def ridgeSupport864_suffix_000 : List Nat := ridgeSupport864_000 ++ ridgeSupport864_suffix_001
theorem ridgeSupport864_source : candidateRows 864 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport864_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
