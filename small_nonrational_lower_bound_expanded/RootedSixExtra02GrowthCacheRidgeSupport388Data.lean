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
def ridgeSupport388_000 : List Nat := [18,34,60,63,66,138,139,140,141,148,149,335,336,337,340,341,346,347,352,354,397,398,402,404,405,409,411,412,414,532,533,534]
def ridgeSupport388_001 : List Nat := [537,538,543,544,549,551,594,595,599,601,602,606,608,609,611,880,884,885,886,887,889,890,897,899,945,946,947,950,951,952,954,959]
def ridgeSupport388_002 : List Nat := [961,964,967,968,969,972,973,974,976,981,982,984,985,1629,1631,1648,1650,1708,1709,1714,1715,1728,1729,1731,1734,1737,1740,1742,1743,1756,1757,1762]
def ridgeSupport388_003 : List Nat := [1763,1797,1799,1804,1805,1810,1811,1816,1818,1824,1825,1838,1839,1848,1849,1862,1863,1869,1871,1888,1890,1948,1949,1954,1955,1968,1969,1971,1974,1977,1980,1982]
def ridgeSupport388_004 : List Nat := [1983,1996,1997,2002,2003,2037,2039,2044,2045,2050,2051,2056,2058,2064,2065,2078,2079,2088,2089,2102,2103,2116,2118,2128,2130,2144,2145,2156,2157,2331,2333,2343]
def ridgeSupport388_005 : List Nat := [2345,2364,2365,2376,2377,3189,3191,3208,3210,3220,3221,3226,3227,3268,3269,3274,3275,3288,3289,3291,3294,3297,3300,3302,3303,3309,3311,3316,3317,3322,3323,3328]
def ridgeSupport388_006 : List Nat := [3330,3364,3365,3370,3371,3388,3389,3394,3395,3694,3695,3706,3707,4798,4799,4806,4807,5145,5147,5152,5154,5157,5159,5164,5166,5168,5169,5190,5191,5240,5242,5249]
def ridgeSupport388_007 : List Nat := [5251,5412,5413,5448,5449,5606,5607,5908,5909,5914,5915,5924,5926,5928,5929,5932,5935,5956,5957,5962,5963,5972,5974,5976,5977,5980,5983,5996,5997,5999,6001,6050]
def ridgeSupport388_008 : List Nat := [6052,6054,6055,6243,6246,6249,6252,6272,6274,6276,6277,6280,6283]
cert_ridgeSupport_code_3 388
cert_ridgeSupport_rest_2 388 000 0
cert_ridgeSupport_rest_2 388 001 416
cert_ridgeSupport_rest_2 388 002 832
cert_ridgeSupport_rest_2 388 003 1248
cert_ridgeSupport_rest_2 388 004 1664
cert_ridgeSupport_rest_2 388 005 2080
cert_ridgeSupport_rest_2 388 006 2496
cert_ridgeSupport_rest_2 388 007 2912
cert_ridgeSupport_rest_2 388 008 3328
cert_ridgeSupport_rest_2 388 009 3497
cert_ridgeSupport_suffix_4 388 009
cert_ridgeSupport_suffix_3 388 008 009
cert_ridgeSupport_suffix_3 388 007 008
cert_ridgeSupport_suffix_3 388 006 007
cert_ridgeSupport_suffix_3 388 005 006
cert_ridgeSupport_suffix_3 388 004 005
cert_ridgeSupport_suffix_3 388 003 004
cert_ridgeSupport_suffix_3 388 002 003
cert_ridgeSupport_suffix_3 388 001 002
cert_ridgeSupport_suffix_3 388 000 001
cert_ridgeSupport_source_3 388 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
