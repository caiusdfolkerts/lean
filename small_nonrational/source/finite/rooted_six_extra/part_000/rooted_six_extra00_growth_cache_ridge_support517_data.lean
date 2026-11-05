module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport517_000 : List Nat := [4,18,21,23,24,154,157,158,161,164,178,181,182,185,188,190,193,194,197,200,382,384,387,388,390,406,408,411,412,414,418,420]
def ridgeSupport517_001 : List Nat := [423,424,426,451,452,454,455,458,459,460,462,463,465,470,471,472,473,475,476,479,480,481,483,484,486,491,492,493,494,496,497,500]
def ridgeSupport517_002 : List Nat := [501,502,504,505,507,512,513,2108,2109,2114,2115,2120,2121,2122,2123,2124,2125,2126,2127,2132,2133,2138,2139,2144,2145,2146,2147,2148,2149,2150,2151,2170]
def ridgeSupport517_003 : List Nat := [2171,2172,2173,2174,2175,2194,2195,2196,2197,2198,2199,2218,2219,2220,2221,2222,2223,2242,2243,2244,2245,2246,2247,2266,2267,2268,2269,2270,2271,2290,2291,2292]
def ridgeSupport517_004 : List Nat := [2293,2294,2295,2296,2298,2302,2304,2308,2310,2314,2315,2316,2317,2318,2319,2666,2667,2684,2685,2702,2703,2704,2706,2710,2712,2720,2721,2738,2739,2756,2757,2774]
def ridgeSupport517_005 : List Nat := [2775,2776,2778,2782,2784,2792,2793,2810,2811,2828,2829,2846,2847,2848,2850,2854,2856,2864,2865,3956,3957,3968,3969,3992,3993,4004,4005,4012,4014,4018,4020,4028]
def ridgeSupport517_006 : List Nat := [4029,4040,4041,4064,4065,4076,4077,4084,4086,4090,4092,4100,4101,4112,4113,4136,4137,4148,4149,4156,4158,4162,4164,7102,7103,7104,7105,7106,7107,7738,7739,7740]
def ridgeSupport517_007 : List Nat := [7741,7742,7743,7744,7746,7750,7752,7754,7755,7756,7758,7762,7764,7766,7767,7834,7836,7850,7851,7852,7854,7868,7869,7870,7872,7886,7887,8128,8130,8134,8136,8146]
def ridgeSupport517_008 : List Nat := [8148,8152,8154,8164,8166,8170,8172]
def ridgeSupport517_code : Nat := 0x1fec7fa9fe67f91fda7f61fd47f49fc87f19fc27f01ecf7b39ec07af9ebd7af1eae7ab1eab7aa9e9c7a69e577959e547949e4e7931e4b7929e487919e427901e3f78f9e3d78f1e3b78e9bc36f09bc16f01bbf6ef9044410903e40f103540d102940a101140410054010ffc3fe8ff63fd0fed3fb0fe13f80fc93f20fbd3ef0fb43ec8fae3eb0fa53e90f993e60f813e00f753dd0b312cc0b282c98b222c80b1f2c78b0d2c30afb2be8ae92ba0ae02b78ada2b60ad72b58ac52b10ab32ac8aa12a80a982a58a922a40a8f2a38a7d29f0a6b29a890f243890d243090b2428906241090023f88fa23e08f723d88f523d08f323c88df23788dd23708db23688c723188c523108c323088af22b88ad22b08ab22a889722588952250893224887f21f887d21f087b21e8867219886521908632188861218085b2168855215084f213884d213084b21288492120843210883d20f020108001fb07e41f807d81f507d01f107c01ee07b41ec07ac1e607901e307841e0077c1dc076c1d907601d707581d1073c1ce07301cb07281c707181c4070c1aa06a01a706901a2067819c066c19806581860610183060017e03200c503080c102f80bc02e40b602d40b202900a1027809d0268018005c0150048004
def ridgeSupport517_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport517_code
def ridgeSupport517_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport517_code
def ridgeSupport517_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport517_code
def ridgeSupport517_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport517_code
def ridgeSupport517_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport517_code
def ridgeSupport517_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport517_code
def ridgeSupport517_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport517_code
def ridgeSupport517_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport517_code
def ridgeSupport517_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport517_code
def ridgeSupport517_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport517_code
def ridgeSupport517_suffix_009 : List Nat := []
def ridgeSupport517_suffix_008 : List Nat := ridgeSupport517_008 ++ ridgeSupport517_suffix_009
def ridgeSupport517_suffix_007 : List Nat := ridgeSupport517_007 ++ ridgeSupport517_suffix_008
def ridgeSupport517_suffix_006 : List Nat := ridgeSupport517_006 ++ ridgeSupport517_suffix_007
def ridgeSupport517_suffix_005 : List Nat := ridgeSupport517_005 ++ ridgeSupport517_suffix_006
def ridgeSupport517_suffix_004 : List Nat := ridgeSupport517_004 ++ ridgeSupport517_suffix_005
def ridgeSupport517_suffix_003 : List Nat := ridgeSupport517_003 ++ ridgeSupport517_suffix_004
def ridgeSupport517_suffix_002 : List Nat := ridgeSupport517_002 ++ ridgeSupport517_suffix_003
def ridgeSupport517_suffix_001 : List Nat := ridgeSupport517_001 ++ ridgeSupport517_suffix_002
def ridgeSupport517_suffix_000 : List Nat := ridgeSupport517_000 ++ ridgeSupport517_suffix_001
theorem ridgeSupport517_source : candidateSupports 517 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport517_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
