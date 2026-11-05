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
def ridgeSupport322_000 : List Nat := [10,40,50,56,61,63,142,143,146,147,150,151,214,215,218,219,222,223,274,276,278,280,282,287,288,290,293,316,317,321,323,324]
def ridgeSupport322_001 : List Nat := [328,330,331,333,637,638,639,640,641,642,696,698,700,701,703,705,706,710,715,739,740,741,744,745,746,748,753,755,793,794,795,796]
def ridgeSupport322_002 : List Nat := [797,798,852,854,856,857,859,861,862,866,871,895,896,897,900,901,902,904,909,911,936,938,940,941,943,945,946,950,955,979,980,981]
def ridgeSupport322_003 : List Nat := [984,985,986,988,993,995,1020,1022,1023,1025,1026,1028,1030,1031,1033,1034,1038,1039,1871,1873,1882,1887,1938,1939,1948,1949,1961,1964,1970,1971,1975,1977]
def ridgeSupport322_004 : List Nat := [1980,1981,1986,1987,1996,1997,2034,2035,2039,2041,2044,2045,2050,2055,2066,2067,2076,2077,2090,2091,2100,2101,2375,2377,2386,2391,2394,2395,2404,2405,2442,2443]
def ridgeSupport322_005 : List Nat := [2452,2453,2465,2468,2474,2475,2479,2481,2484,2485,2490,2491,2495,2497,2500,2501,2506,2511,2538,2539,2548,2549,2562,2563,2572,2573,2584,2589,2614,2619,2628,2629]
def ridgeSupport322_006 : List Nat := [2646,2647,2729,2731,2759,2761,2774,2775,2792,2793,3143,3145,3154,3159,3162,3163,3172,3173,3210,3211,3220,3221,3233,3236,3242,3243,3247,3249,3252,3253,3258,3259]
def ridgeSupport322_007 : List Nat := [3263,3265,3268,3269,3274,3279,3306,3307,3316,3317,3330,3331,3340,3341,3352,3357,3382,3387,3396,3397,3414,3415,3497,3499,3527,3529,3542,3543,3560,3561,4199,4201]
def ridgeSupport322_008 : List Nat := [4210,4215,4218,4219,4228,4229,4266,4267,4276,4277,4289,4292,4298,4299,4303,4305,4308,4309,4314,4315,4319,4321,4324,4325,4330,4335,4362,4363,4372,4373,4386,4387]
def ridgeSupport322_009 : List Nat := [4396,4397,4660,4665,4672,4677,4704,4705,4716,4717,4805,4807,4817,4819,4850,4851,4862,4863,5188,5193,5200,5205,5232,5233,5244,5245,5333,5335,5345,5347,5378,5379]
def ridgeSupport322_010 : List Nat := [5390,5391,7080,7081,7146,7147,7242,7243,7362,7363,7674,7675,7684,7685,7698,7699,7702,7704,7705,7706,7769,7772,7783,7785,7806,7807,7810,7812,7813,7814,7823,7824]
def ridgeSupport322_011 : List Nat := [7825,7826,7858,7860,7862,7863,7937,7940,7951,7953,7974,7975,7978,7980,7981,7982,7991,7992,7993,7994,8026,8028,8030,8031,8177,8180,8191,8193,8214,8215,8218,8220]
def ridgeSupport322_012 : List Nat := [8221,8222,8285,8286,8287,8288,8320,8322,8324,8325,8405,8406,8407,8408,8440,8442,8444,8445]
def ridgeSupport322_code : Nat := 0x83f60fc83ea0f883620d7835a0d58216084820a080818205f817a05d807a01d807201a805e0168005fff7fd1ff17d7df5e7d71f5a7ce9f397ce1f377cb9f2d7cb1f2a7c9df267c45f0f7c11f017addeb67ad1eb27a49e917a41e8f7a19e857a11e8279fde7e79a5e677971e597869e197861e16784de127815e0477eddfa730dcc2712dc4a6fadbea6ea5ba8543d50e540d502538d4e1535d4d551f547c51c5470515545051254444bfd2fe4bcd2f24b4d2d14b1d2c549b526c4985260491524048e523444b512c448d1224455114442d10a43bd0ea43950e443850df436d0da43550d443450cf432d0ca43110c142d50b442ad0aa421508441ed07a41dd07241a506737a4de8375cdd63724dc736acda9355cd563514d4434ecd363474d183434d0c340cd0233d4cf433accea333ccca3314cc43304cbf32eccba32d4cb432c4caf32accaa3290ca13254c94322cc8a3194c64316cc5a315cc523124c472ba4ae82b5cad62b24ac72aacaa9295ca562914a4428eca362874a182834a0c280ca0227d49f427ac9ea273c9ca27149c427049bf26ec9ba26d49b426c49af26ac9aa26909a12654994262c98a2594964256c95a255c952252494720d483420ac82a207481c204c812201c8021ff47fc1fe47f71fcc7f21f347cc1f0c7c21ef47bc1ee47b71ecc7b21eb07a91e7479c1e4c7921d7c75a1d4474f103c40e1028409101c406101040210043ff0ff83fc0f8c3e10f703da0f643d80f543d40f4c3bb0ed83b20ec43af0eb43ac0ea83a80e3c38d0e203860e143840e043800dfc3670d8835e0d7435b0d643580d583540c7831d0c7031b0c683190bcc2f10bb02ea0ba42e80b942e40b8c2cb0b182c20b042bf0af42bc0ae82b80a082810a0027f09f827d053414b05281480510143050413d04f01250488120047c11a04601160450112037c0de036c0da035c0d6025c096024c092023c08e00fc03d00e003200a000a
def ridgeSupport322_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport322_code
def ridgeSupport322_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport322_code
def ridgeSupport322_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport322_code
def ridgeSupport322_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport322_code
def ridgeSupport322_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport322_code
def ridgeSupport322_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport322_code
def ridgeSupport322_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport322_code
def ridgeSupport322_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport322_code
def ridgeSupport322_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport322_code
def ridgeSupport322_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport322_code
def ridgeSupport322_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport322_code
def ridgeSupport322_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport322_code
def ridgeSupport322_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport322_code
def ridgeSupport322_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport322_code
def ridgeSupport322_suffix_013 : List Nat := []
def ridgeSupport322_suffix_012 : List Nat := ridgeSupport322_012 ++ ridgeSupport322_suffix_013
def ridgeSupport322_suffix_011 : List Nat := ridgeSupport322_011 ++ ridgeSupport322_suffix_012
def ridgeSupport322_suffix_010 : List Nat := ridgeSupport322_010 ++ ridgeSupport322_suffix_011
def ridgeSupport322_suffix_009 : List Nat := ridgeSupport322_009 ++ ridgeSupport322_suffix_010
def ridgeSupport322_suffix_008 : List Nat := ridgeSupport322_008 ++ ridgeSupport322_suffix_009
def ridgeSupport322_suffix_007 : List Nat := ridgeSupport322_007 ++ ridgeSupport322_suffix_008
def ridgeSupport322_suffix_006 : List Nat := ridgeSupport322_006 ++ ridgeSupport322_suffix_007
def ridgeSupport322_suffix_005 : List Nat := ridgeSupport322_005 ++ ridgeSupport322_suffix_006
def ridgeSupport322_suffix_004 : List Nat := ridgeSupport322_004 ++ ridgeSupport322_suffix_005
def ridgeSupport322_suffix_003 : List Nat := ridgeSupport322_003 ++ ridgeSupport322_suffix_004
def ridgeSupport322_suffix_002 : List Nat := ridgeSupport322_002 ++ ridgeSupport322_suffix_003
def ridgeSupport322_suffix_001 : List Nat := ridgeSupport322_001 ++ ridgeSupport322_suffix_002
def ridgeSupport322_suffix_000 : List Nat := ridgeSupport322_000 ++ ridgeSupport322_suffix_001
theorem ridgeSupport322_source : candidateSupports 322 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport322_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
