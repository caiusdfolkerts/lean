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
def ridgeSupport515_000 : List Nat := [4,8,11,13,14,154,156,159,160,162,178,180,183,184,186,190,192,195,196,198,226,228,231,232,234,250,252,255,256,258,262,264]
def ridgeSupport515_001 : List Nat := [267,268,270,295,296,298,299,302,303,304,306,307,309,314,315,316,317,319,320,323,324,325,327,328,330,335,336,337,338,340,341,344]
def ridgeSupport515_002 : List Nat := [345,346,348,349,351,356,357,1868,1869,1874,1875,1880,1881,1882,1883,1884,1885,1886,1887,1892,1893,1898,1899,1904,1905,1906,1907,1908,1909,1910,1911,1930]
def ridgeSupport515_003 : List Nat := [1931,1932,1933,1934,1935,1954,1955,1956,1957,1958,1959,1978,1979,1980,1981,1982,1983,2002,2003,2004,2005,2006,2007,2026,2027,2028,2029,2030,2031,2050,2051,2052]
def ridgeSupport515_004 : List Nat := [2053,2054,2055,2056,2058,2062,2064,2068,2070,2074,2075,2076,2077,2078,2079,2660,2661,2672,2673,2696,2697,2708,2709,2716,2718,2722,2724,2732,2733,2744,2745,2768]
def ridgeSupport515_005 : List Nat := [2769,2780,2781,2788,2790,2794,2796,2804,2805,2816,2817,2840,2841,2852,2853,2860,2862,2866,2868,3428,3429,3440,3441,3464,3465,3476,3477,3484,3486,3490,3492,3500]
def ridgeSupport515_006 : List Nat := [3501,3512,3513,3536,3537,3548,3549,3556,3558,3562,3564,3572,3573,3584,3585,3608,3609,3620,3621,3628,3630,3634,3636,7066,7067,7068,7069,7070,7071,7690,7691,7692]
def ridgeSupport515_007 : List Nat := [7693,7694,7695,7696,7698,7702,7704,7706,7707,7708,7710,7714,7716,7718,7719,7840,7842,7846,7848,7858,7860,7864,7866,7876,7878,7882,7884,8008,8010,8014,8016,8026]
def ridgeSupport515_008 : List Nat := [8028,8032,8034,8044,8046,8050,8052]
def ridgeSupport515_code : Nat := 0x1f747dc9f6e7db1f627d81f5c7d69f507d39f4a7d21ecc7b29ec67b11eba7ae1eb47ac9ea87a99ea27a81e277899e247889e1e7871e1b7869e187859e127841e0f7839e0d7831e0b7829b9f6e79b9d6e71b9b6e68e3438c8e2e38b0e253890e193860e013800df537d0dec37a8de63790ddd3770dd13740db936e0dad36b0da43688d9e3670d953650d893620d7135c0d653590b342cc8b2e2cb0b252c90b192c60b012c00af52bd0aec2ba8ae62b90add2b70ad12b40ab92ae0aad2ab0aa42a88a9e2a70a952a50a892a20a7129c0a65299081f207881d207081b20688162050810203880a20208072018805201080320087ef1fb87ed1fb07eb1fa87d71f587d51f507d31f487bf1ef87bd1ef07bb1ee87a71e987a51e907a31e8878f1e3878d1e3078b1e287771dd87751dd07731dc87711dc076b1da87651d9075f1d7875d1d7075b1d687591d607531d4874d1d30165059015f057415c0568159056015505501520544150053c14a05201470514144050c14004fc13d04f013b04e813504cc13204c012f04b812b04a8128049c10e043010b0420106040810003fc0fc03e80ea03a00e703900e203180c4030c0c002f80ba02e00b702d00b202880a0027c09c026800e003400b0020004
def ridgeSupport515_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport515_code
def ridgeSupport515_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport515_code
def ridgeSupport515_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport515_code
def ridgeSupport515_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport515_code
def ridgeSupport515_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport515_code
def ridgeSupport515_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport515_code
def ridgeSupport515_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport515_code
def ridgeSupport515_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport515_code
def ridgeSupport515_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport515_code
def ridgeSupport515_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport515_code
def ridgeSupport515_suffix_009 : List Nat := []
def ridgeSupport515_suffix_008 : List Nat := ridgeSupport515_008 ++ ridgeSupport515_suffix_009
def ridgeSupport515_suffix_007 : List Nat := ridgeSupport515_007 ++ ridgeSupport515_suffix_008
def ridgeSupport515_suffix_006 : List Nat := ridgeSupport515_006 ++ ridgeSupport515_suffix_007
def ridgeSupport515_suffix_005 : List Nat := ridgeSupport515_005 ++ ridgeSupport515_suffix_006
def ridgeSupport515_suffix_004 : List Nat := ridgeSupport515_004 ++ ridgeSupport515_suffix_005
def ridgeSupport515_suffix_003 : List Nat := ridgeSupport515_003 ++ ridgeSupport515_suffix_004
def ridgeSupport515_suffix_002 : List Nat := ridgeSupport515_002 ++ ridgeSupport515_suffix_003
def ridgeSupport515_suffix_001 : List Nat := ridgeSupport515_001 ++ ridgeSupport515_suffix_002
def ridgeSupport515_suffix_000 : List Nat := ridgeSupport515_000 ++ ridgeSupport515_suffix_001
theorem ridgeSupport515_source : candidateSupports 515 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport515_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
