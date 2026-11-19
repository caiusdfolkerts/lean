module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport321_000 : List Nat := [10,16,22,27,29,116,117,118,119,120,121,188,189,190,191,192,193,247,249,251,252,254,256,257,261,266,290,291,292,295,296,297]
def ridgeSupport321_001 : List Nat := [299,304,306,335,337,339,340,342,344,345,349,354,378,379,380,383,384,385,387,392,394,419,421,423,424,426,428,429,433,438,462,463]
def ridgeSupport321_002 : List Nat := [464,467,468,469,471,476,478,503,505,506,508,509,511,513,514,516,517,521,522,1419,1421,1430,1435,1438,1439,1448,1449,1486,1487,1496,1497,1509]
def ridgeSupport321_003 : List Nat := [1512,1518,1519,1523,1525,1528,1529,1534,1535,1539,1541,1544,1545,1550,1555,1582,1583,1592,1593,1606,1607,1616,1617,1659,1661,1670,1675,1678,1679,1688,1689,1726]
def ridgeSupport321_004 : List Nat := [1727,1736,1737,1749,1752,1758,1759,1763,1765,1768,1769,1774,1775,1779,1781,1784,1785,1790,1795,1822,1823,1832,1833,1846,1847,1856,1857,2120,2125,2132,2137,2164]
def ridgeSupport321_005 : List Nat := [2165,2176,2177,2265,2267,2277,2279,2310,2311,2322,2323,2427,2429,2438,2443,2446,2447,2456,2457,2494,2495,2504,2505,2517,2520,2526,2527,2531,2533,2536,2537,2542]
def ridgeSupport321_006 : List Nat := [2543,2547,2549,2552,2553,2558,2563,2590,2591,2600,2601,2614,2615,2624,2625,2888,2893,2900,2905,2932,2933,2944,2945,3033,3035,3045,3047,3078,3079,3090,3091,3666]
def ridgeSupport321_007 : List Nat := [3667,3670,3671,5132,5137,5138,5142,5144,5149,5150,5154,5169,5172,5180,5182,5192,5197,5198,5202,5217,5220,5228,5230,5374,5375,5410,5411,5506,5507,5853,5856,5867]
def ridgeSupport321_008 : List Nat := [5869,5890,5891,5894,5896,5897,5898,5901,5904,5915,5917,5938,5939,5942,5944,5945,5946,6009,6010,6011,6012,6044,6046,6048,6049,6069,6072,6083,6085,6106,6107,6110]
def ridgeSupport321_009 : List Nat := [6112,6113,6114,6177,6178,6179,6180,6212,6214,6216,6217]
cert_ridgeSupport_code_3 321
cert_ridgeSupport_rest_2 321 000 0
cert_ridgeSupport_rest_2 321 001 416
cert_ridgeSupport_rest_2 321 002 832
cert_ridgeSupport_rest_2 321 003 1248
cert_ridgeSupport_rest_2 321 004 1664
cert_ridgeSupport_rest_2 321 005 2080
cert_ridgeSupport_rest_2 321 006 2496
cert_ridgeSupport_rest_2 321 007 2912
cert_ridgeSupport_rest_2 321 008 3328
cert_ridgeSupport_rest_2 321 009 3744
cert_ridgeSupport_rest_2 321 010 3887
cert_ridgeSupport_suffix_4 321 010
cert_ridgeSupport_suffix_3 321 009 010
cert_ridgeSupport_suffix_3 321 008 009
cert_ridgeSupport_suffix_3 321 007 008
cert_ridgeSupport_suffix_3 321 006 007
cert_ridgeSupport_suffix_3 321 005 006
cert_ridgeSupport_suffix_3 321 004 005
cert_ridgeSupport_suffix_3 321 003 004
cert_ridgeSupport_suffix_3 321 002 003
cert_ridgeSupport_suffix_3 321 001 002
cert_ridgeSupport_suffix_3 321 000 001
cert_ridgeSupport_source_3 321 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
