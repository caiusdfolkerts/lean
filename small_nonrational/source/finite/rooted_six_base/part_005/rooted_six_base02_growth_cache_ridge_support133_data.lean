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
def ridgeSupport133_000 : List Nat := [2,15,18,19,102,105,106,109,112,139,140,143,144,149,151,152,155,156,161,331,334,336,337,339,340,342,344,345,347,348,351,352]
def ridgeSupport133_001 : List Nat := [355,357,358,360,361,363,365,366,368,369,372,373,398,399,401,402,403,404,406,407,409,410,412,413,1628,1629,1634,1635,1636,1637,1638,1639]
def ridgeSupport133_002 : List Nat := [1642,1643,1648,1649,1652,1653,1658,1659,1660,1661,1662,1663,1666,1667,1672,1673,1682,1683,1684,1685,1686,1687,1706,1707,1708,1709,1710,1711,1730,1731,1732,1733]
def ridgeSupport133_003 : List Nat := [1734,1735,1754,1755,1756,1757,1758,1759,1778,1779,1780,1781,1782,1783,1802,1803,1804,1805,1806,1807,1823,1825,1826,1827,1828,1829,1830,1831,1833,1836,1839,1842]
def ridgeSupport133_004 : List Nat := [2116,2117,2134,2135,2152,2153,2157,2160,2163,2166,2170,2171,2188,2189,2206,2207,2224,2225,2229,2232,2235,2238,2242,2243,2330,2331,2348,2349,2366,2367,2375,2377]
def ridgeSupport133_005 : List Nat := [2381,2383,2384,2385,3645,3647,3649,3651,3654,3658,3692,3694,3696,3698,3703,3707,3708,3710,3712,3714,3719,3723,5264,5265,5270,5271,5272,5273,5276,5277,5282,5283]
def ridgeSupport133_006 : List Nat := [5284,5285,5294,5295,5296,5297,5298,5299,5318,5319,5320,5321,5322,5323,5339,5341,5342,5343,5344,5345,5346,5347,5349,5352,5355,5358,5363,5365,5366,5367,5368,5369]
def ridgeSupport133_007 : List Nat := [5370,5371,5373,5376,5379,5382,5384,5385,5390,5392,5393,5395,5536,5537,5541,5544,5547,5550,5554,5555,5564,5569,5572,5573,5577,5580,5590,5591,5595,5598,5601,5604]
def ridgeSupport133_008 : List Nat := [5608,5609,5618,5623,5626,5627,5631,5634,5696,5697,5705,5707,5711,5713,5714,5715,5728,5730,5732,5733,5741,5743,6489,6491,6500,6502,6504,6506,7376,7377,7382,7383]
def ridgeSupport133_009 : List Nat := [7384,7385,7400,7405,7406,7411,7420,7422,7622,7623,7624,7625,7626,7627,7881,7892,7896]
def ridgeSupport133_code : Nat := 0x1ed8f6a7b27b97dcaee4f723b8fdc6e7f73f39e7ceee76f3a39b3cd8e6bf35b9a3cd0cb565a32cd964cade566cdf66db32d992cc5660b29d94aca364fb25d926c83640b0157febf75faafbd7cabd35e8af25786bbd5dbaebd75ab995c9ae2d712b835bcad9d6cab5d5abad45696b435a0a89d446a2150ea84d422a0d503a8053f69f74faa7cd3e29ef4f6a7ad3ce9dd4eba7453969c74e2a70d3829bf4dea6ed36e9974caa64d32298f4c6a59d2ca9634b0a57d2ba94b4a4a51d28a93b49ca4cd26292f496a48d241d16e877413a01cfce7c73db9ddce4e7073739b1c94e46721b905c7ee3d4a8a54129e94d4a4a51d27e93e496a4b123691a461a30917c8bb45c22d51628b044fa27911a88c43da1e90ec87343821b50d286842ba15908a8443991cbce587293939c98e4a7243919c88e4271f3879c38e1a70c3859c28dee6f637a9bd0de66f236f9b78dba6dc36d9b68d8e6c63629b10d866c23579ab8d5a6ac3559aa8d2e69634a9a50d266923449a20d0668233f99f8cfa67c33d99e8cea67433899c0cd666a3339998cca6643319988cba65c0ce86703341990cb86583281930c9064431e18e0ba85d02e21700b705b42d61690b405982ca1630b0057c2b815b0ac85602ac1540a985442a014e0a5828413809b04c025c12a090047823011607003681a80d2066009804801e002
def ridgeSupport133_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport133_code
def ridgeSupport133_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport133_code
def ridgeSupport133_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport133_code
def ridgeSupport133_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport133_code
def ridgeSupport133_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport133_code
def ridgeSupport133_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport133_code
def ridgeSupport133_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport133_code
def ridgeSupport133_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport133_code
def ridgeSupport133_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport133_code
def ridgeSupport133_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport133_code
def ridgeSupport133_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport133_code
def ridgeSupport133_suffix_010 : List Nat := []
def ridgeSupport133_suffix_009 : List Nat := ridgeSupport133_009 ++ ridgeSupport133_suffix_010
def ridgeSupport133_suffix_008 : List Nat := ridgeSupport133_008 ++ ridgeSupport133_suffix_009
def ridgeSupport133_suffix_007 : List Nat := ridgeSupport133_007 ++ ridgeSupport133_suffix_008
def ridgeSupport133_suffix_006 : List Nat := ridgeSupport133_006 ++ ridgeSupport133_suffix_007
def ridgeSupport133_suffix_005 : List Nat := ridgeSupport133_005 ++ ridgeSupport133_suffix_006
def ridgeSupport133_suffix_004 : List Nat := ridgeSupport133_004 ++ ridgeSupport133_suffix_005
def ridgeSupport133_suffix_003 : List Nat := ridgeSupport133_003 ++ ridgeSupport133_suffix_004
def ridgeSupport133_suffix_002 : List Nat := ridgeSupport133_002 ++ ridgeSupport133_suffix_003
def ridgeSupport133_suffix_001 : List Nat := ridgeSupport133_001 ++ ridgeSupport133_suffix_002
def ridgeSupport133_suffix_000 : List Nat := ridgeSupport133_000 ++ ridgeSupport133_suffix_001
theorem ridgeSupport133_source : candidateSupports 133 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport133_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
