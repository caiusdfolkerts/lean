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
def ridgeSupport262_000 : List Nat := [3,32,34,36,115,116,118,123,125,139,140,142,147,149,162,165,167,170,172,529,531,532,534,535,538,539,540,542,543,545,550,551]
def ridgeSupport262_001 : List Nat := [573,575,576,578,579,581,583,584,586,587,590,591,594,596,597,599,600,602,604,605,607,608,611,612,1870,1871,1876,1877,1880,1881,1882,1883]
def ridgeSupport262_002 : List Nat := [1884,1885,1890,1891,1894,1895,1900,1901,1904,1905,1906,1907,1908,1909,1914,1915,1928,1929,1930,1931,1932,1933,1952,1953,1954,1955,1956,1957,1976,1977,1978,1979]
def ridgeSupport262_003 : List Nat := [1980,1981,2000,2001,2002,2003,2004,2005,2024,2025,2026,2027,2028,2029,2048,2049,2050,2051,2052,2053,2061,2064,2067,2070,2072,2073,2074,2075,2076,2077,2078,2080]
def ridgeSupport262_004 : List Nat := [2130,2131,2142,2143,2144,2146,2150,2152,2166,2167,2178,2179,2272,2273,2284,2285,2289,2292,2295,2298,2308,2309,2320,2321,2344,2345,2356,2357,2361,2364,2367,2370]
def ridgeSupport262_005 : List Nat := [2380,2381,2392,2393,4765,4767,4769,4771,4774,4778,4797,4799,4801,4803,4806,4810,4828,4830,4832,4834,4839,4843,5398,5399,5402,5403,5406,5407,5410,5411,5414,5415]
def ridgeSupport262_006 : List Nat := [5418,5419,5432,5433,5434,5435,5436,5437,5456,5457,5458,5459,5460,5461,5469,5472,5475,5478,5480,5481,5482,5483,5484,5485,5486,5488,5493,5496,5499,5502,5504,5505]
def ridgeSupport262_007 : List Nat := [5506,5507,5508,5509,5510,5512,5516,5518,5519,5521,5526,5527,5528,5530,5534,5536,5550,5551,5562,5563,5564,5566,5570,5572,5577,5579,5637,5640,5643,5646,5656,5657]
def ridgeSupport262_008 : List Nat := [5668,5669,5673,5676,5679,5682,5684,5689,5691,5694,5697,5700,5710,5711,5722,5723,5727,5730,5733,5736,5738,5743,7129,7131,7137,7139,7144,7146,7390,7391,7394,7395]
def ridgeSupport262_009 : List Nat := [7398,7399,7400,7402,7413,7416,7419,7422,7664,7665,7666,7667,7668,7669,8041,8049,8056]
def ridgeSupport262_code : Nat := 0x1f78fb8fda7bebdf4ef9f7cbbe3df0e7f73ef9f1cf5e7573a39cfce6e71f38b9bfcdedf56fa37c7be1dedef66cdf66ab345996cc565fb2dd96ac9f64eb225906c7d63bb1cd8d2c6562fb1658a6c4b624b0cd862c1d60bb045816b975c9ae2570ab7d5bcaddd6eab5f5aead0567ab35598acbd65ab2358fac75632b11586ac2d612b07582ac0d602afd57babc55d6ae156eab6d5b2ad756aab4d5a2acd563ab05576aab554aa9d54aaa3550a9ed4f2a7753aa9cd4e2a5752aa93d49aa47522a8fd47aa3751aa8bd45a5d72e79714b825bd2dc9654b1a5872c195fcaf65552a6951ca8653f29d4aca56129a94c4a124fd27893949aa4d1252928488a44120a90447d23dd1e88f1476a3b11c28e0441a2090ee87643421990c486042fa1790a6852410207903a81c40da06903281840b204d02080d402a011006802400a000fda7ec3f59fa8fd27e83ea9f50fa67d23e89f40f7a7bc3dd9ee8f727b83d29e90f467a23d09e80f1a78c3c59e28f127883bd9de8eea7743b99dc8ee27703b69db0ece7663b19d88eba75c3ad9d68eb27583aa9d50e9e74e132098c4c025f12e89704b425812b89544a8252127893849624a124091c48a243121090047e23d113889844221f10f087043621a10b885842821310882b01540a7052828812a093047023011607d03d81d80e80730120088040003
def ridgeSupport262_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport262_code
def ridgeSupport262_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport262_code
def ridgeSupport262_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport262_code
def ridgeSupport262_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport262_code
def ridgeSupport262_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport262_code
def ridgeSupport262_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport262_code
def ridgeSupport262_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport262_code
def ridgeSupport262_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport262_code
def ridgeSupport262_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport262_code
def ridgeSupport262_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport262_code
def ridgeSupport262_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport262_code
def ridgeSupport262_suffix_010 : List Nat := []
def ridgeSupport262_suffix_009 : List Nat := ridgeSupport262_009 ++ ridgeSupport262_suffix_010
def ridgeSupport262_suffix_008 : List Nat := ridgeSupport262_008 ++ ridgeSupport262_suffix_009
def ridgeSupport262_suffix_007 : List Nat := ridgeSupport262_007 ++ ridgeSupport262_suffix_008
def ridgeSupport262_suffix_006 : List Nat := ridgeSupport262_006 ++ ridgeSupport262_suffix_007
def ridgeSupport262_suffix_005 : List Nat := ridgeSupport262_005 ++ ridgeSupport262_suffix_006
def ridgeSupport262_suffix_004 : List Nat := ridgeSupport262_004 ++ ridgeSupport262_suffix_005
def ridgeSupport262_suffix_003 : List Nat := ridgeSupport262_003 ++ ridgeSupport262_suffix_004
def ridgeSupport262_suffix_002 : List Nat := ridgeSupport262_002 ++ ridgeSupport262_suffix_003
def ridgeSupport262_suffix_001 : List Nat := ridgeSupport262_001 ++ ridgeSupport262_suffix_002
def ridgeSupport262_suffix_000 : List Nat := ridgeSupport262_000 ++ ridgeSupport262_suffix_001
theorem ridgeSupport262_source : candidateSupports 262 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport262_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
