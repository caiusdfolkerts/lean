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
def ridgeSupport196_000 : List Nat := [15,31,57,63,64,102,103,104,105,112,113,334,335,339,341,342,346,348,349,351,355,356,360,362,363,367,369,370,372,531,532,536]
def ridgeSupport196_001 : List Nat := [538,539,543,545,546,548,552,553,557,559,560,564,566,567,569,882,883,884,887,888,889,891,896,898,903,904,905,908,909,910,912,917]
def ridgeSupport196_002 : List Nat := [919,966,967,969,970,971,972,974,975,977,978,980,981,1641,1643,1647,1649,1700,1701,1706,1707,1727,1729,1733,1735,1740,1741,1746,1747,1748,1749,1754]
def ridgeSupport196_003 : List Nat := [1755,1796,1797,1802,1803,1809,1811,1815,1817,1836,1837,1842,1843,1860,1861,1866,1867,1881,1883,1887,1889,1940,1941,1946,1947,1967,1969,1973,1975,1980,1981,1986]
def ridgeSupport196_004 : List Nat := [1987,1988,1989,1994,1995,2036,2037,2042,2043,2049,2051,2055,2057,2076,2077,2082,2083,2100,2101,2106,2107,2115,2117,2127,2129,2148,2149,2160,2161,2187,2189,2199]
def ridgeSupport196_005 : List Nat := [2201,2220,2221,2232,2233,3201,3203,3207,3209,3212,3213,3218,3219,3260,3261,3266,3267,3287,3289,3293,3295,3300,3301,3306,3307,3308,3309,3314,3315,3321,3323,3327]
def ridgeSupport196_006 : List Nat := [3329,3356,3357,3362,3363,3380,3381,3386,3387,3646,3647,3658,3659,4750,4751,4758,4759,5147,5149,5151,5153,5159,5161,5163,5165,5172,5173,5178,5179,5242,5244,5246]
def ridgeSupport196_007 : List Nat := [5248,5418,5419,5454,5455,5600,5601,5900,5901,5906,5907,5924,5925,5930,5931,5934,5935,5948,5949,5954,5955,5972,5973,5978,5979,5982,5983,5996,5998,6000,6001,6014]
def ridgeSupport196_008 : List Nat := [6016,6018,6019,6239,6241,6245,6247,6272,6273,6278,6279,6282,6283]
cert_ridgeSupport_code_3 196
cert_ridgeSupport_rest_2 196 000 0
cert_ridgeSupport_rest_2 196 001 416
cert_ridgeSupport_rest_2 196 002 832
cert_ridgeSupport_rest_2 196 003 1248
cert_ridgeSupport_rest_2 196 004 1664
cert_ridgeSupport_rest_2 196 005 2080
cert_ridgeSupport_rest_2 196 006 2496
cert_ridgeSupport_rest_2 196 007 2912
cert_ridgeSupport_rest_2 196 008 3328
cert_ridgeSupport_rest_2 196 009 3497
cert_ridgeSupport_suffix_4 196 009
cert_ridgeSupport_suffix_3 196 008 009
cert_ridgeSupport_suffix_3 196 007 008
cert_ridgeSupport_suffix_3 196 006 007
cert_ridgeSupport_suffix_3 196 005 006
cert_ridgeSupport_suffix_3 196 004 005
cert_ridgeSupport_suffix_3 196 003 004
cert_ridgeSupport_suffix_3 196 002 003
cert_ridgeSupport_suffix_3 196 001 002
cert_ridgeSupport_suffix_3 196 000 001
cert_ridgeSupport_source_3 196 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
