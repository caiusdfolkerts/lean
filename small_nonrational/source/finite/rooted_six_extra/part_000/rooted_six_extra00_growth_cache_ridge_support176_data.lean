module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport176_000 : List Nat := [76,96,115,118,119,1201,1202,1204,1209,1211,1236,1239,1241,1244,1246,1248,1251,1253,1256,1258,1466,1467,1469,1474,1476,1501,1504,1506,1509,1511,1513,1516]
def ridgeSupport176_001 : List Nat := [1518,1521,1523,1730,1732,1733,1735,1736,1738,1740,1741,1743,1744,1747,1748,1751,1753,1754,1756,1757,1759,1761,1762,1764,1765,1768,1769,1794,1795,1797,1798,1799]
def ridgeSupport176_002 : List Nat := [1800,1802,1803,1805,1806,1808,1809,6232,6233,6238,6239,6240,6241,6242,6243,6246,6247,6252,6253,6256,6257,6262,6263,6264,6265,6266,6267,6270,6271,6276,6277,6286]
def ridgeSupport176_003 : List Nat := [6287,6288,6289,6290,6291,6310,6311,6312,6313,6314,6315,6334,6335,6336,6337,6338,6339,6358,6359,6360,6361,6362,6363,6382,6383,6384,6385,6386,6387,6406,6407,6408]
def ridgeSupport176_004 : List Nat := [6409,6410,6411,6427,6429,6430,6431,6432,6433,6434,6435,6437,6440,6443,6446,6492,6493,6504,6505,6509,6512,6515,6518,6528,6529,6540,6541,6564,6565,6576,6577,6581]
def ridgeSupport176_005 : List Nat := [6584,6587,6590,6600,6601,6612,6613,6706,6707,6718,6719,6727,6729,6733,6735,6742,6743,6754,6755,6780,6781,6792,6793,6797,6800,6803,6806,6816,6817,6828,6829,6852]
def ridgeSupport176_006 : List Nat := [6853,6864,6865,6869,6872,6875,6878,6888,6889,6900,6901,6994,6995,7006,7007,7015,7017,7021,7023,7030,7031,7042,7043,7594,7595,7596,7597,7598,7599,8638,8639,8640]
def ridgeSupport176_007 : List Nat := [8641,8642,8643,8659,8661,8662,8663,8664,8665,8671,8673,8674,8675,8676,8677,8682,8683,8688,8689,8700,8701,8706,8707,8734,8735,8740,8741,8754,8755,8760,8761,8772]
def ridgeSupport176_008 : List Nat := [8773,8778,8779,8806,8807,8812,8813]
def ridgeSupport176_code : Nat := 0x226d89b2267899a24b892a245891223988e223388ca225889221f887a203880a1fd87f21f187c21eb87aa1e587921e3878a1e1877e1d987621d7875a1d5874e1c3870a1c187021bf86f9daf76b9dad76b1dab76a9b836e09b776dd9b6f6db5b696d9db5f6d79b536d49af56bd1ae96ba1ade6b6dad86b55ad16b41ac56b11aad6ab1aa16a81a966a4da906a35a896a21a7d69f1a636989a576959a4f6935a49691da3f68f9a3368c99d567519c967219be66ed9b866d59b166c19a5669198d6631981660197665cd97065b596965a195d657192e64ad92864959236489921648191f647991d646d90b6429909642190764198f363c98f163c18ef63b98db63698d963618d763598c363098c163018bf62f98ab62a98a962a18a762998936249891624188f6239885621187f61f987b61e987961e187761d987161c186d61b186761998636189861618185f617985961607111c4070e1c3470b1c287081c1c7061c147031c086e91ba06e51b906e21b846df1b746dc1b686d91b5c6d41b4c6d01b3c6cd1b306ca1b206c71b146c41b085f317c45ee17b05e9179c5e517885e017745c417085bd16ec5ba13a84e813944e313804de13704d9135c4d412ec4b912d04b212c407701d8073018004c
def ridgeSupport176_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport176_code
def ridgeSupport176_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport176_code
def ridgeSupport176_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport176_code
def ridgeSupport176_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport176_code
def ridgeSupport176_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport176_code
def ridgeSupport176_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport176_code
def ridgeSupport176_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport176_code
def ridgeSupport176_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport176_code
def ridgeSupport176_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport176_code
def ridgeSupport176_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport176_code
def ridgeSupport176_suffix_009 : List Nat := []
def ridgeSupport176_suffix_008 : List Nat := ridgeSupport176_008 ++ ridgeSupport176_suffix_009
def ridgeSupport176_suffix_007 : List Nat := ridgeSupport176_007 ++ ridgeSupport176_suffix_008
def ridgeSupport176_suffix_006 : List Nat := ridgeSupport176_006 ++ ridgeSupport176_suffix_007
def ridgeSupport176_suffix_005 : List Nat := ridgeSupport176_005 ++ ridgeSupport176_suffix_006
def ridgeSupport176_suffix_004 : List Nat := ridgeSupport176_004 ++ ridgeSupport176_suffix_005
def ridgeSupport176_suffix_003 : List Nat := ridgeSupport176_003 ++ ridgeSupport176_suffix_004
def ridgeSupport176_suffix_002 : List Nat := ridgeSupport176_002 ++ ridgeSupport176_suffix_003
def ridgeSupport176_suffix_001 : List Nat := ridgeSupport176_001 ++ ridgeSupport176_suffix_002
def ridgeSupport176_suffix_000 : List Nat := ridgeSupport176_000 ++ ridgeSupport176_suffix_001
theorem ridgeSupport176_source : candidateSupports 176 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport176_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
