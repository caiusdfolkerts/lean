module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public meta import CertificateNumbers
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
cert_ridgeSupport_2 133 7384 7385 7400 7405 7406 7411 7420 7422 7622 7623 7624 7625 7626 7627 7881 7892 7896
cert_ridgeSupport_code_2 133
cert_ridgeSupport_rest 133 000 0
cert_ridgeSupport_rest 133 001 416
cert_ridgeSupport_rest 133 002 832
cert_ridgeSupport_rest 133 003 1248
cert_ridgeSupport_rest 133 004 1664
cert_ridgeSupport_rest 133 005 2080
cert_ridgeSupport_rest 133 006 2496
cert_ridgeSupport_rest 133 007 2912
cert_ridgeSupport_rest 133 008 3328
cert_ridgeSupport_rest 133 009 3744
cert_ridgeSupport_rest 133 010 3965
cert_ridgeSupport_suffix_2 133 010
cert_ridgeSupport_suffix 133 009 010
cert_ridgeSupport_suffix 133 008 009
cert_ridgeSupport_suffix 133 007 008
cert_ridgeSupport_suffix 133 006 007
cert_ridgeSupport_suffix 133 005 006
cert_ridgeSupport_suffix 133 004 005
cert_ridgeSupport_suffix 133 003 004
cert_ridgeSupport_suffix 133 002 003
cert_ridgeSupport_suffix 133 001 002
cert_ridgeSupport_suffix 133 000 001
cert_ridgeSupport_source 133 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
