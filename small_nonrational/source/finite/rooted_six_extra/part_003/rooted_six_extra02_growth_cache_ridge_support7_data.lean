module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport7_000 : List Nat := [0,1,2,3,4,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128]
def ridgeSupport7_001 : List Nat := [129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160]
def ridgeSupport7_002 : List Nat := [161,162,163,164,165,166,167,168,169,170,171,172,173,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126]
def ridgeSupport7_003 : List Nat := [2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151,2152,2153,2154,2155,2156,2157,2158]
def ridgeSupport7_004 : List Nat := [2159,2160,2161,2162,2163,2164,2165,2166,2167,2168,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184,2185,2186,2187,2188,2189,2190]
def ridgeSupport7_005 : List Nat := [2191,2192,2193,2194,2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222]
def ridgeSupport7_006 : List Nat := [2223,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254]
def ridgeSupport7_007 : List Nat := [2255,2256,2257,2258,2259,2260,2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286]
def ridgeSupport7_008 : List Nat := [2287,2288,2289,2290,2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318]
def ridgeSupport7_009 : List Nat := [2319,2320,2321,2322,2323,2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348,2349,2350]
def ridgeSupport7_010 : List Nat := [2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,2372,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382]
def ridgeSupport7_011 : List Nat := [2383,2384,2385,2386,2387,2388,2389,2390,2391,2392,2393,2394,2395,5168,5169,5170,5171,5172,5173,5174,5175,5176,5177,5178,5179,5180,5181,5182,5183,5184,5185,5186]
def ridgeSupport7_012 : List Nat := [5187,5188,5189,5190,5191,5456,5457,5458,5459,5460,5461,5462,5463,5464,5465,5466,5467,5468,5469,5470,5471,5472,5473,5474,5475,5476,5477,5478,5479,5996,5997,5998]
def ridgeSupport7_013 : List Nat := [5999,6000,6001,6002,6003,6004,6005,6006,6007,6008,6009,6010,6011,6012,6013,6014,6015,6016,6017,6018,6019,6020,6021,6022,6023,6024,6025,6026,6027,6028,6029,6030]
def ridgeSupport7_014 : List Nat := [6031,6032,6033,6034,6035,6036,6037,6038,6039,6040,6041,6042,6043,6044,6045,6046,6047,6048,6049,6050,6051,6052,6053,6054,6055,6056,6057,6058,6059,6060,6061,6062]
def ridgeSupport7_015 : List Nat := [6063,6064,6065,6066,6067]
def ridgeSupport7_code : Nat := 0x17b3bd95ec6f617afbd75eb6f597abbd55ea6f517a7bd35e96f497a3bd15e86f4179fbcf5e76f3979bbcd5e66f31797bcb5e56f29793bc95e46f2178fbc75e36f1978bbc55e26f11787bc35e16f09783bc15e06f0177fbbf5df6ef977bbbd5de6ef1777bbb5dd6ee9773bb95dc6ee176fbb75db6ed9567ab35596ac9563ab15586ac155faaf5576ab955baad5566ab1557aab5556aa9553aa95546aa1447a235116889443a21510688143fa1f50f687943ba1d50e6871437a1b50d6869433a1950c686095b4ad25652b09574ab25552a89534a925452a094f4a7253529894b4a525252909474a325152889434a1250528093f49f24f527893b49d24e527093749b24d526893349924c526092f49724b525892b49524a52509274932495248923491248524091f48f247523891b48d246523091748b2455228913489244522090f487243521890b4852425210907483241520890348124052008ff47f23f51f88fb47d23e51f08f747b23d51e88f347923c51e08ef47723b51d88eb47523a51d08e747323951c88e347123851c08df46f23751b88db46d23651b08d746b23551a88d346923451a08cf46723351988cb46523251908c746323151888c346123051808bf45f22f51788bb45d22e51708b745b22d51688b345922c51608af45722b51588ab45522a51508a745322951488a3451228514089f44f227513889b44d226513089744b2255128893449224512088f447223511888b44522251108874432215108883441220510087f43f21f50f887b43d21e50f087743b21d50e887343921c50e086f43721b50d886b43521a50d086743321950c886343121850c085f42f21750b885b42d21650b085742b21550a885342921450a084f427213509884b42521250908474232115088843421210508083f41f20f50780ad05602ac1540a9054029c14c0a5052028c1440a1050027c13c09d04e026c13409904c025c12c09504a024c124091048023c11c08d046022c114089044021c10c085042020c10408104001fc0fc07d03e01ec0f407903c01dc0ec07503a01cc0e407103801bc0dc06d03601ac0d4069034019c0cc0040018008002000
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
def ridgeSupport7_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport7_code
def ridgeSupport7_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport7_code
def ridgeSupport7_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport7_code
def ridgeSupport7_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport7_code
def ridgeSupport7_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport7_code
def ridgeSupport7_rest_016 : Nat := PackedRawNatGrowth.drop 6305 ridgeSupport7_code
def ridgeSupport7_suffix_016 : List Nat := []
def ridgeSupport7_suffix_015 : List Nat := ridgeSupport7_015 ++ ridgeSupport7_suffix_016
def ridgeSupport7_suffix_014 : List Nat := ridgeSupport7_014 ++ ridgeSupport7_suffix_015
def ridgeSupport7_suffix_013 : List Nat := ridgeSupport7_013 ++ ridgeSupport7_suffix_014
def ridgeSupport7_suffix_012 : List Nat := ridgeSupport7_012 ++ ridgeSupport7_suffix_013
def ridgeSupport7_suffix_011 : List Nat := ridgeSupport7_011 ++ ridgeSupport7_suffix_012
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
    (PackedRawNatGrowth.readList 13 485 ridgeSupport7_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
