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
def ridgeSupport672_000 : List Nat := [89,109,119,126,128,1092,1093,1094,1095,1102,1103,1248,1249,1250,1251,1258,1259,1378,1379,1380,1383,1384,1389,1390,1395,1397,1419,1421,1423,1425,1427,1432]
def ridgeSupport672_001 : List Nat := [1433,1435,1438,1513,1514,1515,1516,1523,1524,1643,1644,1645,1648,1649,1654,1655,1660,1662,1684,1686,1688,1690,1692,1697,1698,1700,1703,1752,1753,1754,1757,1758]
def ridgeSupport672_002 : List Nat := [1763,1764,1769,1771,1793,1795,1797,1799,1801,1806,1807,1809,1812,1839,1841,1843,1845,1846,1848,1850,1851,1855,1857,1862,1863,5464,5469,5478,5480,5546,5547,5556]
def ridgeSupport672_003 : List Nat := [5557,5562,5563,5566,5568,5572,5573,5579,5582,5594,5595,5604,5605,5632,5637,5642,5643,5646,5648,5652,5653,5658,5659,5668,5669,5682,5683,5692,5693,5704,5709,5718]
def ridgeSupport672_004 : List Nat := [5720,5786,5787,5796,5797,5802,5803,5806,5808,5812,5813,5819,5822,5834,5835,5844,5845,5872,5877,5882,5883,5886,5888,5892,5893,5898,5899,5908,5909,5922,5923,5932]
def ridgeSupport672_005 : List Nat := [5933,6024,6026,6036,6038,6052,6053,6064,6065,6166,6171,6178,6183,6198,6199,6210,6211,6232,6237,6246,6248,6314,6315,6324,6325,6330,6331,6334,6336,6340,6341,6347]
def ridgeSupport672_006 : List Nat := [6350,6362,6363,6372,6373,6400,6405,6410,6411,6414,6416,6420,6421,6426,6427,6436,6437,6450,6451,6460,6461,6552,6554,6564,6566,6580,6581,6592,6593,6694,6699,6706]
def ridgeSupport672_007 : List Nat := [6711,6726,6727,6738,6739,6840,6842,6852,6854,6868,6869,6880,6881,6982,6987,6994,6999,7014,7015,7026,7027,7518,7519,7554,7555,7614,7615,8474,8475,8484,8485,8489]
def ridgeSupport672_008 : List Nat := [8490,8491,8492,8497,8498,8522,8523,8532,8533,8537,8538,8539,8540,8545,8546,8578,8579,8581,8583,8615,8616,8617,8618,8642,8643,8652,8653,8657,8658,8659,8660,8665]
def ridgeSupport672_009 : List Nat := [8666,8698,8699,8701,8703,8735,8736,8737,8738,8770,8771,8773,8775,8807,8808,8809,8810]
def ridgeSupport672_code : Nat := 0x226a89a6268899e2478916243890a2228886220887e1ff87f61fb87ea1da87661d4874e1d287461cd87321c3870a1aa86a61a8869e1878616183860a162858615c856e15a8566155855214b852a13284c612c84ae12a84a6125849211b8469dbf76f9d837609d5f7579b736dc9b676d99b576d49b4b6d19ae16b81ad56b51ac66b11aba6ae1a536949a476919a3768c9a2b68999c167019b566d19a6669199a666193d64f193364c9925649191b64699156451910643990b642990564018e563918db63698ce632d8c563118c062f98bb62e98b562d18ab62a9868619985d6161843610983760d9827608981b60597b15ec17a55e917965e5178a5e2172d5cb17235c897155c5170b5c297055c117005bf96fb5be96f55bc16d55b516cb5b296be5aed6b55ad16b05ab96ab5aa96a55a9169b5a69658595964d592163d58f163358c9625589161b58696155851610583960b582960558015e557915db57695ce572d5c557115c056f95bb56e95b556d15ab56a9568559955d55607471d187411cfc73b1ce87381cd87351ccc7311cbc7141c4470f1c387091c1c7051c0c7011bac6e91b906e31b786dd1b686d91b606a71a906a21a8469c1a686981a5869419f867c19dc67619c467019b466c19ac5f417cc5ec17ac5ea17a459e166c5991660593164458f163458b15d457315b856d15a0567159056315884eb13a84e313884e1138044f11384471118445111008001f807701b4059
def ridgeSupport672_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport672_code
def ridgeSupport672_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport672_code
def ridgeSupport672_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport672_code
def ridgeSupport672_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport672_code
def ridgeSupport672_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport672_code
def ridgeSupport672_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport672_code
def ridgeSupport672_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport672_code
def ridgeSupport672_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport672_code
def ridgeSupport672_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport672_code
def ridgeSupport672_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport672_code
def ridgeSupport672_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport672_code
def ridgeSupport672_suffix_010 : List Nat := []
def ridgeSupport672_suffix_009 : List Nat := ridgeSupport672_009 ++ ridgeSupport672_suffix_010
def ridgeSupport672_suffix_008 : List Nat := ridgeSupport672_008 ++ ridgeSupport672_suffix_009
def ridgeSupport672_suffix_007 : List Nat := ridgeSupport672_007 ++ ridgeSupport672_suffix_008
def ridgeSupport672_suffix_006 : List Nat := ridgeSupport672_006 ++ ridgeSupport672_suffix_007
def ridgeSupport672_suffix_005 : List Nat := ridgeSupport672_005 ++ ridgeSupport672_suffix_006
def ridgeSupport672_suffix_004 : List Nat := ridgeSupport672_004 ++ ridgeSupport672_suffix_005
def ridgeSupport672_suffix_003 : List Nat := ridgeSupport672_003 ++ ridgeSupport672_suffix_004
def ridgeSupport672_suffix_002 : List Nat := ridgeSupport672_002 ++ ridgeSupport672_suffix_003
def ridgeSupport672_suffix_001 : List Nat := ridgeSupport672_001 ++ ridgeSupport672_suffix_002
def ridgeSupport672_suffix_000 : List Nat := ridgeSupport672_000 ++ ridgeSupport672_suffix_001
theorem ridgeSupport672_source : candidateSupports 672 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport672_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
