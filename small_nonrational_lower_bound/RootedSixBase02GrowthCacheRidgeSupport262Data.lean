module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
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
def ridgeSupport262_000 : List Nat := [3,32,34,36,115,116,118,123,125,139,140,142,147,149,162,165,167,170,172,529,531,532,534,535,538,539,540,542,543,545,550,551]
def ridgeSupport262_001 : List Nat := [573,575,576,578,579,581,583,584,586,587,590,591,594,596,597,599,600,602,604,605,607,608,611,612,1870,1871,1876,1877,1880,1881,1882,1883]
def ridgeSupport262_002 : List Nat := [1884,1885,1890,1891,1894,1895,1900,1901,1904,1905,1906,1907,1908,1909,1914,1915,1928,1929,1930,1931,1932,1933,1952,1953,1954,1955,1956,1957,1976,1977,1978,1979]
def ridgeSupport262_003 : List Nat := [1980,1981,2000,2001,2002,2003,2004,2005,2024,2025,2026,2027,2028,2029,2048,2049,2050,2051,2052,2053,2061,2064,2067,2070,2072,2073,2074,2075,2076,2077,2078,2080]
def ridgeSupport262_004 : List Nat := [2130,2131,2142,2143,2144,2146,2150,2152,2166,2167,2178,2179,2272,2273,2284,2285,2289,2292,2295,2298,2308,2309,2320,2321,2344,2345,2356,2357,2361,2364,2367,2370]
def ridgeSupport262_005 : List Nat := [2380,2381,2392,2393,4765,4767,4769,4771,4774,4778,4797,4799,4801,4803,4806,4810,4828,4830,4832,4834,4839,4843,5398,5399,5402,5403,5406,5407,5410,5411,5414,5415]
def ridgeSupport262_006 : List Nat := [5418,5419,5432,5433,5434,5435,5436,5437,5456,5457,5458,5459,5460,5461,5469,5472,5475,5478,5480,5481,5482,5483,5484,5485,5486,5488,5493,5496,5499,5502,5504,5505]
def ridgeSupport262_007 : List Nat := [5506,5507,5508,5509,5510,5512,5516,5518,5519,5521,5526,5527,5528,5530,5534,5536,5550,5551,5562,5563,5564,5566,5570,5572,5577,5579,5637,5640,5643,5646,5656,5657]
def ridgeSupport262_008 : List Nat := [5668,5669,5673,5676,5679,5682,5684,5689,5691,5694,5697,5700,5710,5711,5722,5723,5727,5730,5733,5736,5738,5743,7129,7131,7137,7139,7144,7146,7390,7391,7394,7395]
cert_ridgeSupport_2 262 7398 7399 7400 7402 7413 7416 7419 7422 7664 7665 7666 7667 7668 7669 8041 8049 8056
cert_ridgeSupport_code_2 262
cert_ridgeSupport_rest 262 000 0
cert_ridgeSupport_rest 262 001 416
cert_ridgeSupport_rest 262 002 832
cert_ridgeSupport_rest 262 003 1248
cert_ridgeSupport_rest 262 004 1664
cert_ridgeSupport_rest 262 005 2080
cert_ridgeSupport_rest 262 006 2496
cert_ridgeSupport_rest 262 007 2912
cert_ridgeSupport_rest 262 008 3328
cert_ridgeSupport_rest 262 009 3744
cert_ridgeSupport_rest 262 010 3965
cert_ridgeSupport_suffix_2 262 010
cert_ridgeSupport_suffix 262 009 010
cert_ridgeSupport_suffix 262 008 009
cert_ridgeSupport_suffix 262 007 008
cert_ridgeSupport_suffix 262 006 007
cert_ridgeSupport_suffix 262 005 006
cert_ridgeSupport_suffix 262 004 005
cert_ridgeSupport_suffix 262 003 004
cert_ridgeSupport_suffix 262 002 003
cert_ridgeSupport_suffix 262 001 002
cert_ridgeSupport_suffix 262 000 001
cert_ridgeSupport_source 262 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
