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
def ridgeSupport67_000 : List Nat := [1,5,9,10,11,103,105,106,109,111,115,117,118,121,123,127,129,130,133,135,175,177,178,181,183,187,189,190,193,195,199,201]
def ridgeSupport67_001 : List Nat := [202,205,207,247,248,250,251,252,253,255,256,258,259,261,262,268,269,271,272,273,274,276,277,279,280,282,283,289,290,292,293,294]
def ridgeSupport67_002 : List Nat := [295,297,298,300,301,303,304,1388,1389,1390,1391,1392,1393,1394,1395,1400,1401,1406,1407,1412,1413,1414,1415,1416,1417,1418,1419,1424,1425,1430,1431,1436]
def ridgeSupport67_003 : List Nat := [1437,1438,1439,1440,1441,1460,1461,1462,1463,1464,1465,1484,1485,1486,1487,1488,1489,1508,1509,1510,1511,1512,1513,1532,1533,1534,1535,1536,1537,1556,1557,1558]
def ridgeSupport67_004 : List Nat := [1559,1560,1561,1580,1581,1582,1583,1584,1585,1589,1591,1595,1597,1601,1603,2108,2109,2120,2121,2144,2145,2156,2157,2171,2173,2177,2179,2180,2181,2192,2193,2216]
def ridgeSupport67_005 : List Nat := [2217,2228,2229,2243,2245,2249,2251,2252,2253,2264,2265,2288,2289,2300,2301,2315,2317,2321,2323,2876,2877,2888,2889,2912,2913,2924,2925,2939,2941,2945,2947,2948]
def ridgeSupport67_006 : List Nat := [2949,2960,2961,2984,2985,2996,2997,3011,3013,3017,3019,3020,3021,3032,3033,3056,3057,3068,3069,3083,3085,3089,3091,5132,5133,5134,5135,5136,5137,5168,5169,5174]
def ridgeSupport67_007 : List Nat := [5175,5180,5181,5216,5217,5222,5223,5228,5229,5348,5349,5350,5351,5352,5353,5852,5853,5854,5855,5856,5857,5876,5877,5878,5879,5880,5881,5888,5889,5890,5891,5892]
def ridgeSupport67_008 : List Nat := [5893,6005,6007,6011,6013,6023,6025,6029,6031,6041,6043,6047,6049,6173,6175,6179,6181,6191,6193,6197,6199,6209,6211,6215,6217]
def ridgeSupport67_code : Nat := 0x1849c23e10f083837c1ae0c705f825c11e07f03b7a1bcfde6ef3378fbc6de26f0f77dbbddddeeeb705b825c0ee05701b805be6df16f7b7b5bd6de96e1b705b7edbd6ddb6e53a69d14e7a7353969c946da36519e8cd461a3050f6879437a1b50c6861411a08503e81d40da06304d822c0d605aff57f8bf15f82f657b0bcd5e62f2d792bc55e1aed5768ba95d42e45720b855c22e0d702b7d5bdadb56d8b615b02d25690b3d59e244d22290d485a3f51f88f147823651b08cd466232d1928c5461a2d51688a94542245120885442220d10287d43da1b50d8861430212509083d41e190cc8263d31d98dcc6a63131818bcc5c62d3161864c3061730b1854c2860130017fcbfc5fd2fe17a4bd05e72f31794bc85d12e8173cb9c5cd2e616e4b705b72db16d4b685a12d0167cb3c59d2ce165cb2c5912c8162cb145892c4161cb0c5852c215fcafc5792bc15ccae45712b815bcadc56d2b604c025e12d09604a82521270930494248122090846c23411808b8454228112088844021e10d086041820a10308104001fe0fd07e03ec1f40f807b833c19a0ca064831c1860c105f02f41760b705a82c81620af043821410408103f81ec0f207603a81cc0de06d03501a40ce00b005002400a001
def ridgeSupport67_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport67_code
def ridgeSupport67_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport67_code
def ridgeSupport67_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport67_code
def ridgeSupport67_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport67_code
def ridgeSupport67_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport67_code
def ridgeSupport67_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport67_code
def ridgeSupport67_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport67_code
def ridgeSupport67_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport67_code
def ridgeSupport67_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport67_code
def ridgeSupport67_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport67_code
def ridgeSupport67_suffix_009 : List Nat := []
def ridgeSupport67_suffix_008 : List Nat := ridgeSupport67_008 ++ ridgeSupport67_suffix_009
def ridgeSupport67_suffix_007 : List Nat := ridgeSupport67_007 ++ ridgeSupport67_suffix_008
def ridgeSupport67_suffix_006 : List Nat := ridgeSupport67_006 ++ ridgeSupport67_suffix_007
def ridgeSupport67_suffix_005 : List Nat := ridgeSupport67_005 ++ ridgeSupport67_suffix_006
def ridgeSupport67_suffix_004 : List Nat := ridgeSupport67_004 ++ ridgeSupport67_suffix_005
def ridgeSupport67_suffix_003 : List Nat := ridgeSupport67_003 ++ ridgeSupport67_suffix_004
def ridgeSupport67_suffix_002 : List Nat := ridgeSupport67_002 ++ ridgeSupport67_suffix_003
def ridgeSupport67_suffix_001 : List Nat := ridgeSupport67_001 ++ ridgeSupport67_suffix_002
def ridgeSupport67_suffix_000 : List Nat := ridgeSupport67_000 ++ ridgeSupport67_suffix_001
theorem ridgeSupport67_source : candidateSupports 67 =
    (PackedRawNatGrowth.readList 13 281 ridgeSupport67_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
