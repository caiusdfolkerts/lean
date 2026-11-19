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
def ridgeSupport385_000 : List Nat := [12,18,24,27,30,140,141,142,143,144,145,212,213,214,215,216,217,246,250,251,252,253,255,256,263,265,311,312,313,316,317,318]
def ridgeSupport385_001 : List Nat := [320,325,327,334,338,339,340,341,343,344,351,353,399,400,401,404,405,406,408,413,415,418,422,423,424,425,427,428,435,437,483,484]
def ridgeSupport385_002 : List Nat := [485,488,489,490,492,497,499,502,505,506,507,510,511,512,514,519,520,522,523,1413,1415,1432,1434,1444,1445,1450,1451,1492,1493,1498,1499,1512]
def ridgeSupport385_003 : List Nat := [1513,1515,1518,1521,1524,1526,1527,1533,1535,1540,1541,1546,1547,1552,1554,1588,1589,1594,1595,1612,1613,1618,1619,1653,1655,1672,1674,1684,1685,1690,1691,1732]
def ridgeSupport385_004 : List Nat := [1733,1738,1739,1752,1753,1755,1758,1761,1764,1766,1767,1773,1775,1780,1781,1786,1787,1792,1794,1828,1829,1834,1835,1852,1853,1858,1859,2122,2124,2134,2136,2162]
def ridgeSupport385_005 : List Nat := [2163,2174,2175,2337,2339,2349,2351,2382,2383,2394,2395,2421,2423,2440,2442,2452,2453,2458,2459,2500,2501,2506,2507,2520,2521,2523,2526,2529,2532,2534,2535,2541]
def ridgeSupport385_006 : List Nat := [2543,2548,2549,2554,2555,2560,2562,2596,2597,2602,2603,2620,2621,2626,2627,2890,2892,2902,2904,2930,2931,2942,2943,3105,3107,3117,3119,3150,3151,3162,3163,3698]
def ridgeSupport385_007 : List Nat := [3699,3702,3703,5132,5134,5141,5143,5144,5146,5153,5155,5171,5173,5186,5188,5192,5194,5201,5203,5219,5221,5234,5236,5378,5379,5414,5415,5510,5511,5859,5862,5865]
def ridgeSupport385_008 : List Nat := [5868,5888,5890,5892,5893,5896,5899,5907,5910,5913,5916,5936,5938,5940,5941,5944,5947,6008,6009,6011,6013,6062,6064,6066,6067,6075,6078,6081,6084,6104,6106,6108]
def ridgeSupport385_009 : List Nat := [6109,6112,6115,6176,6177,6179,6181,6230,6232,6234,6235]
cert_ridgeSupport_code_3 385
cert_ridgeSupport_rest_2 385 000 0
cert_ridgeSupport_rest_2 385 001 416
cert_ridgeSupport_rest_2 385 002 832
cert_ridgeSupport_rest_2 385 003 1248
cert_ridgeSupport_rest_2 385 004 1664
cert_ridgeSupport_rest_2 385 005 2080
cert_ridgeSupport_rest_2 385 006 2496
cert_ridgeSupport_rest_2 385 007 2912
cert_ridgeSupport_rest_2 385 008 3328
cert_ridgeSupport_rest_2 385 009 3744
cert_ridgeSupport_rest_2 385 010 3887
cert_ridgeSupport_suffix_4 385 010
cert_ridgeSupport_suffix_3 385 009 010
cert_ridgeSupport_suffix_3 385 008 009
cert_ridgeSupport_suffix_3 385 007 008
cert_ridgeSupport_suffix_3 385 006 007
cert_ridgeSupport_suffix_3 385 005 006
cert_ridgeSupport_suffix_3 385 004 005
cert_ridgeSupport_suffix_3 385 003 004
cert_ridgeSupport_suffix_3 385 002 003
cert_ridgeSupport_suffix_3 385 001 002
cert_ridgeSupport_suffix_3 385 000 001
cert_ridgeSupport_source_3 385 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
