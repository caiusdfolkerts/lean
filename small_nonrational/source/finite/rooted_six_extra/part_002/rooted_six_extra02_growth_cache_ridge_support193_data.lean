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
def ridgeSupport193_000 : List Nat := [9,15,21,27,28,104,105,106,107,108,109,176,177,178,179,180,181,248,249,250,253,254,255,257,262,264,269,270,271,274,275,276]
def ridgeSupport193_001 : List Nat := [278,283,285,336,337,338,341,342,343,345,350,352,357,358,359,362,363,364,366,371,373,420,421,422,425,426,427,429,434,436,441,442]
def ridgeSupport193_002 : List Nat := [443,446,447,448,450,455,457,504,505,507,508,509,510,512,513,515,516,518,519,1425,1427,1431,1433,1436,1437,1442,1443,1484,1485,1490,1491,1511]
def ridgeSupport193_003 : List Nat := [1513,1517,1519,1524,1525,1530,1531,1532,1533,1538,1539,1545,1547,1551,1553,1580,1581,1586,1587,1604,1605,1610,1611,1665,1667,1671,1673,1676,1677,1682,1683,1724]
def ridgeSupport193_004 : List Nat := [1725,1730,1731,1751,1753,1757,1759,1764,1765,1770,1771,1772,1773,1778,1779,1785,1787,1791,1793,1820,1821,1826,1827,1844,1845,1850,1851,2121,2123,2133,2135,2166]
def ridgeSupport193_005 : List Nat := [2167,2178,2179,2193,2195,2205,2207,2238,2239,2250,2251,2433,2435,2439,2441,2444,2445,2450,2451,2492,2493,2498,2499,2519,2521,2525,2527,2532,2533,2538,2539,2540]
def ridgeSupport193_006 : List Nat := [2541,2546,2547,2553,2555,2559,2561,2588,2589,2594,2595,2612,2613,2618,2619,2889,2891,2901,2903,2934,2935,2946,2947,2961,2963,2973,2975,3006,3007,3018,3019,3650]
def ridgeSupport193_007 : List Nat := [3651,3654,3655,5134,5136,5138,5140,5146,5148,5150,5152,5168,5170,5174,5176,5194,5196,5198,5200,5216,5218,5222,5224,5372,5373,5408,5409,5504,5505,5855,5857,5861]
def ridgeSupport193_008 : List Nat := [5863,5888,5889,5894,5895,5898,5899,5903,5905,5909,5911,5936,5937,5942,5943,5946,5947,6008,6010,6012,6013,6026,6028,6030,6031,6071,6073,6077,6079,6104,6105,6110]
def ridgeSupport193_009 : List Nat := [6111,6114,6115,6176,6178,6180,6181,6194,6196,6198,6199]
def ridgeSupport193_code : Nat := 0x60df06d834c196097049822c105f8efc57dfbef5f66fb17bfbdedee6f6f78fbc75e32f1577dbbe5deaef173bb9d5cdee6d731b985c5ee2b711b87dc2ee15707b835c06e016e7b72db86dbf581ac05486a414fda7e51a28cd462a30514289d44ca2550e286d432a18508283d41ca0d5052825410a07391dc8ce437212f2d794bbf5df2e7d73ab935c8ae0d704b775bb2d5d6aab4b5a4a8ed474a3551a288d444a1d50e28053fe9fb4fca7cd3e49ed4f627ad3d49e54f2277d3ba9d94eba70d3849bd4de264d32498d4c6262530e9834c0a32d1948bf45f227d13a893448a20d10487743b215d0aa84b4249cece7473539a1c8ce4471d38e1c04dfe6fb37c9bccde46ed3761bacdd46e53721b7cdba6d936b9b0cd846bd35e1a4cd2468d3461a24d0e683340992cc9464532218ccc6462d3161844c1e60b304980cc045fd2fe17ecbf45f52fa17bcbda5e92f3974cba45cd2e6168cb4459d2ce1664b2e5932c8881c40c20410188044001fe0fe87f03f61f90fc072438e1c20e006fc37c1bb0dd06e43681b20d686ac3541a90d306943481750b985b82d816b0b5059c2cc1650b005782b21570ab05542a41510a8047423611608a044c22410f087043421010608083fc1fc0fd07d03e41f00b505a02cc1640b105801b40d806b03501a40d001c00d805401e009
def ridgeSupport193_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport193_code
def ridgeSupport193_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport193_code
def ridgeSupport193_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport193_code
def ridgeSupport193_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport193_code
def ridgeSupport193_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport193_code
def ridgeSupport193_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport193_code
def ridgeSupport193_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport193_code
def ridgeSupport193_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport193_code
def ridgeSupport193_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport193_code
def ridgeSupport193_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport193_code
def ridgeSupport193_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport193_code
def ridgeSupport193_suffix_010 : List Nat := []
def ridgeSupport193_suffix_009 : List Nat := ridgeSupport193_009 ++ ridgeSupport193_suffix_010
def ridgeSupport193_suffix_008 : List Nat := ridgeSupport193_008 ++ ridgeSupport193_suffix_009
def ridgeSupport193_suffix_007 : List Nat := ridgeSupport193_007 ++ ridgeSupport193_suffix_008
def ridgeSupport193_suffix_006 : List Nat := ridgeSupport193_006 ++ ridgeSupport193_suffix_007
def ridgeSupport193_suffix_005 : List Nat := ridgeSupport193_005 ++ ridgeSupport193_suffix_006
def ridgeSupport193_suffix_004 : List Nat := ridgeSupport193_004 ++ ridgeSupport193_suffix_005
def ridgeSupport193_suffix_003 : List Nat := ridgeSupport193_003 ++ ridgeSupport193_suffix_004
def ridgeSupport193_suffix_002 : List Nat := ridgeSupport193_002 ++ ridgeSupport193_suffix_003
def ridgeSupport193_suffix_001 : List Nat := ridgeSupport193_001 ++ ridgeSupport193_suffix_002
def ridgeSupport193_suffix_000 : List Nat := ridgeSupport193_000 ++ ridgeSupport193_suffix_001
theorem ridgeSupport193_source : candidateSupports 193 =
    (PackedRawNatGrowth.readList 13 299 ridgeSupport193_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
