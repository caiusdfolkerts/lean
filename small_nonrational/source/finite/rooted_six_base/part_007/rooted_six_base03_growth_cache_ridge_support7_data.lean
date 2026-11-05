module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport7_000 : List Nat := [0,1,2,3,4,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142]
def ridgeSupport7_001 : List Nat := [143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174]
def ridgeSupport7_002 : List Nat := [175,176,177,178,179,180,181,182,183,184,185,186,187,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040]
def ridgeSupport7_003 : List Nat := [2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072]
def ridgeSupport7_004 : List Nat := [2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2104]
def ridgeSupport7_005 : List Nat := [2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2136]
def ridgeSupport7_006 : List Nat := [2137,2138,2139,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151,2152,2153,2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2168]
def ridgeSupport7_007 : List Nat := [2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184,2185,2186,2187,2188,2189,2190,2191,2192,2193,2194,2195,2196,2197,2198,2199,2200]
def ridgeSupport7_008 : List Nat := [2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2226,2227,2228,2229,2230,2231,2232]
def ridgeSupport7_009 : List Nat := [2233,2234,2235,2236,2237,4434,4435,4436,4437,4438,4439,4440,4441,4442,4443,4444,4445,4446,4447,4448,4449,4450,4451,4452,4453,4454,4455,4456,4457,4782,4783,4784]
def ridgeSupport7_010 : List Nat := [4785,4786,4787,4788,4789,4790,4791,4792,4793,4794,4795,4796,4797,4798,4799,4800,4801,4802,4803,4804,4805]
def ridgeSupport7_code : Nat := 0x12c59624b0e5852c19604afe57d2bd95e4aee5752b995c4ade56d2b595a4ace5652b19584abe55d1698b4459e2cd1658b2458e2c51618b0457e2bd15d8ae456e2b51598ac455e2ad1558aa454e2a48bd45e22ed1748b945c22dd16c8b545a22cd1648b145822bd15c8ad45622ad1548a9454229d14c8a5452228d1448a1450227d13c89d44e226d13489944c225d12c89544a224d124891448223d11c88d446222d114889444221d10c885442220d10488144021fd0fc87d43e21ed0f487943c21dd0ec87543a21cd0e487143821bd0dc86d43621ad0d4869434219d0cc865432218d0c4861430217d0bc85d42e216d0b485942c215d0ac85542a214d0a4851428213d09c84d426212d094849424211d08c845422210d08484142020fd07c83d41e20ed07483941c20dd06c83541a20cd06483141820bd05c82d41620ad054829414209d04c825412208d044821410207d03c81d40e206d03481940c205d02c81540a204d024811408203d01c80d406202d014809404201d00c805402200d0048014001ffcffc7fd3fe1fecff47f93fc1fdcfec7f53fa1fccfe47f13f81fbcfdc7ed3f61facfd47e93f41f9cfcc0bb05d02e41700b705b02d41680b305902c41600af05702b41580ab05502a41500a705302941480a3051028414009f04f027413809b04d026413009704b0254128093049024412008f047023411808b04502241100870430214108083041020410007f03f01f40f807b03d01e40f007703b01d40e80040018008002000
def ridgeSupport7_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport7_code
def ridgeSupport7_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport7_code
def ridgeSupport7_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport7_code
def ridgeSupport7_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport7_code
def ridgeSupport7_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport7_code
def ridgeSupport7_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport7_code
def ridgeSupport7_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport7_code
def ridgeSupport7_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport7_code
def ridgeSupport7_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport7_code
def ridgeSupport7_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport7_code
def ridgeSupport7_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport7_code
def ridgeSupport7_rest_011 : Nat := PackedRawNatGrowth.drop 4433 ridgeSupport7_code
def ridgeSupport7_suffix_011 : List Nat := []
def ridgeSupport7_suffix_010 : List Nat := ridgeSupport7_010 ++ ridgeSupport7_suffix_011
def ridgeSupport7_suffix_009 : List Nat := ridgeSupport7_009 ++ ridgeSupport7_suffix_010
def ridgeSupport7_suffix_008 : List Nat := ridgeSupport7_008 ++ ridgeSupport7_suffix_009
def ridgeSupport7_suffix_007 : List Nat := ridgeSupport7_007 ++ ridgeSupport7_suffix_008
def ridgeSupport7_suffix_006 : List Nat := ridgeSupport7_006 ++ ridgeSupport7_suffix_007
def ridgeSupport7_suffix_005 : List Nat := ridgeSupport7_005 ++ ridgeSupport7_suffix_006
def ridgeSupport7_suffix_004 : List Nat := ridgeSupport7_004 ++ ridgeSupport7_suffix_005
def ridgeSupport7_suffix_003 : List Nat := ridgeSupport7_003 ++ ridgeSupport7_suffix_004
def ridgeSupport7_suffix_002 : List Nat := ridgeSupport7_002 ++ ridgeSupport7_suffix_003
def ridgeSupport7_suffix_001 : List Nat := ridgeSupport7_001 ++ ridgeSupport7_suffix_002
def ridgeSupport7_suffix_000 : List Nat := ridgeSupport7_000 ++ ridgeSupport7_suffix_001
theorem ridgeSupport7_source : candidateSupports 7 =
    (PackedRawNatGrowth.readList 13 341 ridgeSupport7_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
