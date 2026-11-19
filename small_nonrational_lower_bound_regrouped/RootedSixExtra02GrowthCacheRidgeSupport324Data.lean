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
def ridgeSupport324_000 : List Nat := [16,32,58,63,65,114,115,116,117,124,125,334,336,338,340,342,347,348,350,353,376,377,381,383,384,388,390,391,393,531,533,535]
def ridgeSupport324_001 : List Nat := [537,539,544,545,547,550,573,574,578,580,581,585,587,588,590,881,883,885,886,888,890,891,895,900,924,925,926,929,930,931,933,938]
def ridgeSupport324_002 : List Nat := [940,965,967,968,970,971,973,975,976,978,979,983,984,1635,1637,1646,1651,1702,1703,1712,1713,1725,1728,1734,1735,1739,1741,1744,1745,1750,1751,1760]
def ridgeSupport324_003 : List Nat := [1761,1798,1799,1803,1805,1808,1809,1814,1819,1830,1831,1840,1841,1854,1855,1864,1865,1875,1877,1886,1891,1942,1943,1952,1953,1965,1968,1974,1975,1979,1981,1984]
def ridgeSupport324_004 : List Nat := [1985,1990,1991,2000,2001,2038,2039,2043,2045,2048,2049,2054,2059,2070,2071,2080,2081,2094,2095,2104,2105,2114,2119,2126,2131,2146,2147,2158,2159,2259,2261,2271]
def ridgeSupport324_005 : List Nat := [2273,2292,2293,2304,2305,3195,3197,3206,3211,3214,3215,3224,3225,3262,3263,3272,3273,3285,3288,3294,3295,3299,3301,3304,3305,3310,3311,3315,3317,3320,3321,3326]
def ridgeSupport324_006 : List Nat := [3331,3358,3359,3368,3369,3382,3383,3392,3393,3662,3663,3674,3675,4766,4767,4774,4775,5145,5148,5151,5155,5157,5160,5163,5167,5170,5171,5184,5185,5240,5245,5246]
def ridgeSupport324_007 : List Nat := [5250,5416,5417,5452,5453,5602,5603,5902,5903,5912,5913,5926,5927,5930,5932,5933,5934,5950,5951,5960,5961,5974,5975,5978,5980,5981,5982,5997,5998,5999,6000,6032]
def ridgeSupport324_008 : List Nat := [6034,6036,6037,6237,6240,6251,6253,6274,6275,6278,6280,6281,6282]
cert_ridgeSupport_code_3 324
cert_ridgeSupport_rest_2 324 000 0
cert_ridgeSupport_rest_2 324 001 416
cert_ridgeSupport_rest_2 324 002 832
cert_ridgeSupport_rest_2 324 003 1248
cert_ridgeSupport_rest_2 324 004 1664
cert_ridgeSupport_rest_2 324 005 2080
cert_ridgeSupport_rest_2 324 006 2496
cert_ridgeSupport_rest_2 324 007 2912
cert_ridgeSupport_rest_2 324 008 3328
cert_ridgeSupport_rest_2 324 009 3497
cert_ridgeSupport_suffix_4 324 009
cert_ridgeSupport_suffix_3 324 008 009
cert_ridgeSupport_suffix_3 324 007 008
cert_ridgeSupport_suffix_3 324 006 007
cert_ridgeSupport_suffix_3 324 005 006
cert_ridgeSupport_suffix_3 324 004 005
cert_ridgeSupport_suffix_3 324 003 004
cert_ridgeSupport_suffix_3 324 002 003
cert_ridgeSupport_suffix_3 324 001 002
cert_ridgeSupport_suffix_3 324 000 001
cert_ridgeSupport_source_3 324 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
