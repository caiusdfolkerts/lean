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
def ridgeSupport112_000 : List Nat := [75,95,115,116,117,1200,1203,1205,1208,1210,1212,1215,1217,1220,1222,1224,1227,1229,1232,1234,1465,1468,1470,1473,1475,1477,1480,1482,1485,1487,1489,1492]
def ridgeSupport112_001 : List Nat := [1494,1497,1499,1731,1732,1734,1735,1736,1737,1739,1740,1742,1743,1745,1746,1752,1753,1755,1756,1757,1758,1760,1761,1763,1764,1766,1767,1773,1774,1776,1777,1778]
def ridgeSupport112_002 : List Nat := [1779,1781,1782,1784,1785,1787,1788,6232,6233,6234,6235,6236,6237,6238,6239,6244,6245,6250,6251,6256,6257,6258,6259,6260,6261,6262,6263,6268,6269,6274,6275,6280]
def ridgeSupport112_003 : List Nat := [6281,6282,6283,6284,6285,6304,6305,6306,6307,6308,6309,6328,6329,6330,6331,6332,6333,6352,6353,6354,6355,6356,6357,6376,6377,6378,6379,6380,6381,6400,6401,6402]
def ridgeSupport112_004 : List Nat := [6403,6404,6405,6424,6425,6426,6427,6428,6429,6433,6435,6439,6441,6445,6447,6490,6491,6502,6503,6511,6513,6517,6519,6526,6527,6538,6539,6562,6563,6574,6575,6583]
def ridgeSupport112_005 : List Nat := [6585,6589,6591,6598,6599,6610,6611,6634,6635,6646,6647,6655,6657,6661,6663,6670,6671,6682,6683,6778,6779,6790,6791,6799,6801,6805,6807,6814,6815,6826,6827,6850]
def ridgeSupport112_006 : List Nat := [6851,6862,6863,6871,6873,6877,6879,6886,6887,6898,6899,6922,6923,6934,6935,6943,6945,6949,6951,6958,6959,6970,6971,7588,7589,7590,7591,7592,7593,8632,8633,8634]
def ridgeSupport112_007 : List Nat := [8635,8636,8637,8656,8657,8658,8659,8660,8661,8668,8669,8670,8671,8672,8673,8680,8681,8686,8687,8698,8699,8704,8705,8716,8717,8722,8723,8752,8753,8758,8759,8770]
def ridgeSupport112_008 : List Nat := [8771,8776,8777,8788,8789,8794,8795]
def ridgeSupport112_code : Nat := 0x225b896a25589522498922243890a23788da23188c2213884a20d883220188021fb87ea1ef87ba1e987a21e187821df877a1dd87721d587521d3874a1d187421bd86f21bb86ea1b986e1da976a1da77699da57691b3b6ce9b2f6cb9b276c95b216c7db176c59b0b6c29af36bc9ae76b99adf6b75ad96b5dacf6b39ac36b09aab6aa9a9f6a79a976a55a916a3da876a19a7b69e9a1b6869a0f6839a076815a0167fd9f767d99eb67a99d367499c767199bf66f59b966dd9af66b99a3668998b662997f65f997765d597165bd967659995b656992f64b5929649d923648591d647191b646991964619056411903640990164018ed63b18eb63a98e963a18d563518d363498d163418bd62f18bb62e98b962e18a562918a362898a1628188d623188b62298896221883620987d61f187761d987561d187361c987161c186b61a9865619185f617985d617185b616985961606fc1bec6f91be06f61bd46f31bc86f11bc06ee1bb46e71b986e41b8c6e11b806de1b746dc1b6c6d91b606d21b446cf1b386cc1b2c6c91b206c71b186c41b0c5db17645d617505d1173c5cd17285c817145c317045be16f05b913484d013344cb13204c613104c112fc4bc12e84b812d44b312c007501d0073017c04b
def ridgeSupport112_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport112_code
def ridgeSupport112_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport112_code
def ridgeSupport112_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport112_code
def ridgeSupport112_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport112_code
def ridgeSupport112_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport112_code
def ridgeSupport112_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport112_code
def ridgeSupport112_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport112_code
def ridgeSupport112_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport112_code
def ridgeSupport112_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport112_code
def ridgeSupport112_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport112_code
def ridgeSupport112_suffix_009 : List Nat := []
def ridgeSupport112_suffix_008 : List Nat := ridgeSupport112_008 ++ ridgeSupport112_suffix_009
def ridgeSupport112_suffix_007 : List Nat := ridgeSupport112_007 ++ ridgeSupport112_suffix_008
def ridgeSupport112_suffix_006 : List Nat := ridgeSupport112_006 ++ ridgeSupport112_suffix_007
def ridgeSupport112_suffix_005 : List Nat := ridgeSupport112_005 ++ ridgeSupport112_suffix_006
def ridgeSupport112_suffix_004 : List Nat := ridgeSupport112_004 ++ ridgeSupport112_suffix_005
def ridgeSupport112_suffix_003 : List Nat := ridgeSupport112_003 ++ ridgeSupport112_suffix_004
def ridgeSupport112_suffix_002 : List Nat := ridgeSupport112_002 ++ ridgeSupport112_suffix_003
def ridgeSupport112_suffix_001 : List Nat := ridgeSupport112_001 ++ ridgeSupport112_suffix_002
def ridgeSupport112_suffix_000 : List Nat := ridgeSupport112_000 ++ ridgeSupport112_suffix_001
theorem ridgeSupport112_source : candidateSupports 112 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport112_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
