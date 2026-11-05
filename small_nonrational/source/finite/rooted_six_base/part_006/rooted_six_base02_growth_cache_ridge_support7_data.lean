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
def ridgeSupport7_011 : List Nat := [2383,2384,2385,2386,2387,2388,2389,2390,2391,2392,2393,2394,2395,5528,5529,5530,5531,5532,5533,5534,5535,5536,5537,5538,5539,5540,5541,5542,5543,5544,5545,5546]
def ridgeSupport7_012 : List Nat := [5547,5548,5549,5550,5551,5552,5553,5554,5555,5556,5557,5558,5559,5560,5561,5562,5563,5564,5565,5566,5567,5568,5569,5570,5571,5572,5573,5574,5575,5576,5577,5578]
def ridgeSupport7_013 : List Nat := [5579,5580,5581,5582,5583,5584,5585,5586,5587,5588,5589,5590,5591,5592,5593,5594,5595,5596,5597,5598,5599,5600,5601,5602,5603,5604,5605,5606,5607,5608,5609,5610]
def ridgeSupport7_014 : List Nat := [5611,5612,5613,5614,5615,5616,5617,5618,5619,5620,5621,5622,5623,5624,5625,5626,5627,5628,5629,5630,5631,5632,5633,5634,5635,5636,5637,5638,5639,5640,5641,5642]
def ridgeSupport7_015 : List Nat := [5643,5644,5645,5646,5647,5648,5649,5650,5651,5652,5653,5654,5655,5656,5657,5658,5659,5660,5661,5662,5663,5664,5665,5666,5667,5668,5669,5670,5671,5672,5673,5674]
def ridgeSupport7_016 : List Nat := [5675,5676,5677,5678,5679,5680,5681,5682,5683,5684,5685,5686,5687,5688,5689,5690,5691,5692,5693,5694,5695,5696,5697,5698,5699,5700,5701,5702,5703,5704,5705,5706]
def ridgeSupport7_017 : List Nat := [5707,5708,5709,5710,5711,5712,5713,5714,5715,5716,5717,5718,5719,5720,5721,5722,5723,5724,5725,5726,5727,5728,5729,5730,5731,5732,5733,5734,5735,5736,5737,5738]
def ridgeSupport7_018 : List Nat := [5739,5740,5741,5742,5743,7400,7401,7402,7403,7404,7405,7406,7407,7408,7409,7410,7411,7412,7413,7414,7415,7416,7417,7418,7419,7420,7421,7422,7423,7688,7689,7690]
def ridgeSupport7_019 : List Nat := [7691,7692,7693,7694,7695,7696,7697,7698,7699,7700,7701,7702,7703,7704,7705,7706,7707,7708,7709,7710,7711]
def ridgeSupport7_code : Nat := 0x1e1ff0f7877c39e1bf0d7867c31e17f0b7857c29e13f097847c21e0ff077837c19e0bf057827c11cffe7f73f79f9cfbe7d73e79f1cf7e7b73d79e9cf3e7973c79e1cefe7773b79d9cebe7573a79d166fb3759b6cd966bb3559a6cd1667b335996cc9663b315986cc165fb2f5976cb965bb2d5966cb1657b2b5956ca9653b295946ca164fb275936c9964bb255926c91647b235916c89643b215906c8163fb1f58f6c7963bb1d58e6c71637b1b58d6c69633b1958c6c6162fb1758b6c5962bb1558a6c51627b135896c49623b115886c4161fb0f5876c3961bb0d5866c31617b0b5856c29613b095846c2160fb075836c1960bb055826c11607b035816c09603b015806c015ffaff57f6bf95fbafd57e6bf15f7afb57d6be95f3af957c6be15efaf757b6bd95ebaf557a6bd15e7af35796bc95e3af15786bc15dfaef5776bb95dbaed5766bb15d7aeb5756ba95d3ae95746ba15cfae75736b995cbae55726b915c7ae35716b895c3ae15706b815bfadf56f6b795bbadd56e6b715b7adb56d6b695b3ad956c6b615afad756b6b595abad556a6b515a7ad35696b495a3ad15686b4159facf5676b3959bacd5666b3095b4ad25652b09574ab25552a89534a925452a094f4a7253529894b4a525252909474a325152889434a1250528093f49f24f527893b49d24e527093749b24d526893349924c526092f49724b525892b49524a52509274932495248923491248524091f48f247523891b48d246523091748b2455228913489244522090f487243521890b4852425210907483241520890348124052008ff47f23f51f88fb47d23e51f08f747b23d51e88f347923c51e08ef47723b51d88eb47523a51d08e747323951c88e347123851c08df46f23751b88db46d23651b08d746b23551a88d346923451a08cf46723351988cb46523251908c746323151888c346123051808bf45f22f51788bb45d22e51708b745b22d51688b345922c51608af45722b51588ab45522a51508a745322951488a3451228514089f44f227513889b44d226513089744b2255128893449224512088f447223511888b44522251108874432215108883441220510087f43f21f50f887b43d21e50f087743b21d50e887343921c50e086f43721b50d886b43521a50d086743321950c886343121850c085f42f21750b885b42d21650b085742b21550a885342921450a084f427213509884b42521250908474232115088843421210508083f41f20f50780ad05602ac1540a9054029c14c0a5052028c1440a1050027c13c09d04e026c13409904c025c12c09504a024c124091048023c11c08d046022c114089044021c10c085042020c10408104001fc0fc07d03e01ec0f407903c01dc0ec07503a01cc0e407103801bc0dc06d03601ac0d4069034019c0cc0040018008002000
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
def ridgeSupport7_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport7_code
def ridgeSupport7_rest_017 : Nat := PackedRawNatGrowth.drop 7072 ridgeSupport7_code
def ridgeSupport7_rest_018 : Nat := PackedRawNatGrowth.drop 7488 ridgeSupport7_code
def ridgeSupport7_rest_019 : Nat := PackedRawNatGrowth.drop 7904 ridgeSupport7_code
def ridgeSupport7_rest_020 : Nat := PackedRawNatGrowth.drop 8177 ridgeSupport7_code
def ridgeSupport7_suffix_020 : List Nat := []
def ridgeSupport7_suffix_019 : List Nat := ridgeSupport7_019 ++ ridgeSupport7_suffix_020
def ridgeSupport7_suffix_018 : List Nat := ridgeSupport7_018 ++ ridgeSupport7_suffix_019
def ridgeSupport7_suffix_017 : List Nat := ridgeSupport7_017 ++ ridgeSupport7_suffix_018
def ridgeSupport7_suffix_016 : List Nat := ridgeSupport7_016 ++ ridgeSupport7_suffix_017
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
    (PackedRawNatGrowth.readList 13 629 ridgeSupport7_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
