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
def ridgeSupport304_000 : List Nat := [77,97,116,118,120,1213,1214,1216,1221,1223,1237,1238,1240,1245,1247,1260,1263,1265,1268,1270,1478,1479,1481,1486,1488,1502,1503,1505,1510,1512,1525,1528]
def ridgeSupport304_001 : List Nat := [1530,1533,1535,1730,1731,1733,1734,1737,1738,1739,1741,1742,1744,1749,1750,1772,1774,1775,1777,1778,1780,1782,1783,1785,1786,1789,1790,1793,1795,1796,1798,1799]
def ridgeSupport304_002 : List Nat := [1801,1803,1804,1806,1807,1810,1811,6234,6235,6240,6241,6244,6245,6246,6247,6248,6249,6254,6255,6258,6259,6264,6265,6268,6269,6270,6271,6272,6273,6278,6279,6292]
def ridgeSupport304_003 : List Nat := [6293,6294,6295,6296,6297,6316,6317,6318,6319,6320,6321,6340,6341,6342,6343,6344,6345,6364,6365,6366,6367,6368,6369,6388,6389,6390,6391,6392,6393,6412,6413,6414]
def ridgeSupport304_004 : List Nat := [6415,6416,6417,6425,6428,6431,6434,6436,6437,6438,6439,6440,6441,6442,6444,6494,6495,6506,6507,6508,6510,6514,6516,6530,6531,6542,6543,6636,6637,6648,6649,6653]
def ridgeSupport304_005 : List Nat := [6656,6659,6662,6672,6673,6684,6685,6708,6709,6720,6721,6725,6728,6731,6734,6744,6745,6756,6757,6782,6783,6794,6795,6796,6798,6802,6804,6818,6819,6830,6831,6924]
def ridgeSupport304_006 : List Nat := [6925,6936,6937,6941,6944,6947,6950,6960,6961,6972,6973,6996,6997,7008,7009,7013,7016,7019,7022,7032,7033,7044,7045,7600,7601,7602,7603,7604,7605,8644,8645,8646]
def ridgeSupport304_007 : List Nat := [8647,8648,8649,8657,8660,8663,8665,8666,8667,8669,8672,8675,8677,8678,8679,8684,8685,8690,8691,8718,8719,8724,8725,8736,8737,8742,8743,8756,8757,8762,8763,8790]
def ridgeSupport304_008 : List Nat := [8791,8796,8797,8808,8809,8814,8815]
def ridgeSupport304_code : Nat := 0x226f89ba26989a225d8972257895a23b88ea23588d2227889a2218882215885220f883a1f387ca1ed87b21e7879a1e5878e1e087761db876a1d9875e1d487461c987221c7871a1c58711db576d1db376c9db176c1b856e11b796de1b6e6dadb686d95b616d81b556d51b3d6cf1b316cc1b266c8db206c75b196c61b0d6c31aaf6ab9aa36a89a946a49a8e6a31a8b6a29a7f69f9a656991a596961a4e692da486915a416901a3568d1a1d6871a116841a06680da0067f59f967e19ed67b198f6639983660997465c996e65b196b65a995f657992c64a992964a192764999256491922647d91c6465911644190f643990d64318f963e18f763d98f563d18e163818df63798dd63718c963218c763198c563118b162c18af62b98ad62b18996261897625989562518876219881620187f61f987d61f187961e187361c986f61b986961a186761998656191861618185b61687131c4870f1c3870c1c2c7091c1c7061c107031c046fe1bf46fa1be46f71bd86f41bc86f11bbc6ee1bb06d61b546d01b386cd1b2c6ca1b246c61b146c31b085ff17f45fa17e05f517a05e617845df17785d017385c9171c5c613d84f413c44ef13b04df13744d813584d5131c4c513004be12f407801d8074018404d
def ridgeSupport304_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport304_code
def ridgeSupport304_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport304_code
def ridgeSupport304_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport304_code
def ridgeSupport304_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport304_code
def ridgeSupport304_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport304_code
def ridgeSupport304_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport304_code
def ridgeSupport304_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport304_code
def ridgeSupport304_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport304_code
def ridgeSupport304_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport304_code
def ridgeSupport304_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport304_code
def ridgeSupport304_suffix_009 : List Nat := []
def ridgeSupport304_suffix_008 : List Nat := ridgeSupport304_008 ++ ridgeSupport304_suffix_009
def ridgeSupport304_suffix_007 : List Nat := ridgeSupport304_007 ++ ridgeSupport304_suffix_008
def ridgeSupport304_suffix_006 : List Nat := ridgeSupport304_006 ++ ridgeSupport304_suffix_007
def ridgeSupport304_suffix_005 : List Nat := ridgeSupport304_005 ++ ridgeSupport304_suffix_006
def ridgeSupport304_suffix_004 : List Nat := ridgeSupport304_004 ++ ridgeSupport304_suffix_005
def ridgeSupport304_suffix_003 : List Nat := ridgeSupport304_003 ++ ridgeSupport304_suffix_004
def ridgeSupport304_suffix_002 : List Nat := ridgeSupport304_002 ++ ridgeSupport304_suffix_003
def ridgeSupport304_suffix_001 : List Nat := ridgeSupport304_001 ++ ridgeSupport304_suffix_002
def ridgeSupport304_suffix_000 : List Nat := ridgeSupport304_000 ++ ridgeSupport304_suffix_001
theorem ridgeSupport304_source : candidateSupports 304 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport304_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
