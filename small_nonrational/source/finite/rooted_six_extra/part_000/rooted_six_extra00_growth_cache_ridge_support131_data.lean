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
def ridgeSupport131_000 : List Nat := [2,6,9,12,13,130,132,135,136,138,167,169,170,173,175,179,181,182,185,187,202,204,207,208,210,239,241,242,245,247,251,253]
def ridgeSupport131_001 : List Nat := [254,257,259,274,276,277,279,280,282,284,285,287,288,291,292,295,297,298,300,301,303,305,306,308,309,312,313,338,339,341,342,343]
def ridgeSupport131_002 : List Nat := [344,346,347,349,350,352,353,1864,1865,1870,1871,1872,1873,1874,1875,1878,1879,1884,1885,1888,1889,1894,1895,1896,1897,1898,1899,1902,1903,1908,1909,1918]
def ridgeSupport131_003 : List Nat := [1919,1920,1921,1922,1923,1942,1943,1944,1945,1946,1947,1966,1967,1968,1969,1970,1971,1990,1991,1992,1993,1994,1995,2014,2015,2016,2017,2018,2019,2038,2039,2040]
def ridgeSupport131_004 : List Nat := [2041,2042,2043,2059,2061,2062,2063,2064,2065,2066,2067,2069,2072,2075,2078,2586,2587,2598,2599,2622,2623,2634,2635,2645,2648,2651,2654,2658,2659,2670,2671,2694]
def ridgeSupport131_005 : List Nat := [2695,2706,2707,2717,2720,2723,2726,2800,2801,2812,2813,2836,2837,2848,2849,2863,2865,2869,2871,3354,3355,3366,3367,3390,3391,3402,3403,3413,3416,3419,3422,3426]
def ridgeSupport131_006 : List Nat := [3427,3438,3439,3462,3463,3474,3475,3485,3488,3491,3494,3568,3569,3580,3581,3604,3605,3616,3617,3631,3633,3637,3639,7054,7055,7056,7057,7058,7059,7678,7679,7680]
def ridgeSupport131_007 : List Nat := [7681,7682,7683,7699,7701,7702,7703,7704,7705,7711,7713,7714,7715,7716,7717,7823,7826,7829,7832,7841,7844,7847,7850,7879,7881,7885,7887,7991,7994,7997,8000,8009]
def ridgeSupport131_008 : List Nat := [8012,8015,8018,8047,8049,8053,8055]
def ridgeSupport131_code : Nat := 0x1f777dd5f717dbdf527d3df4c7d25f407cf5f3a7cddecf7b35ec97b1deaa7a9dea47a85e987a55e927a3de257891e237889e21787de197861e177859e15784de037809e017801dff77f9b936e49b916e41b8f6e38e3738d4e3138bce213880e153850dfd37f0df137c0da6368cda03674d933648d873618d6f35b8d633588d5e356cd583554d4b3528d3f34f8d273498d1b3468b372cd4b312cbcb212c80b152c50afd2bf0af12bc0aa62a8caa02a74a932a48a872a18a6f29b8a632988a5e296ca582954a4b2928a3f28f8a272898a1b286881e206c81820548132048811204080f203880d202c7fb1fe87f91fe07f71fd87e31f887e11f807df1f787cb1f287c91f207c71f187b31ec87b11ec07af1eb879b1e687991e607971e587831e087811e0077f1df87751dd076f1db876b1da87691da07671d987611d8075d1d707571d587531d487511d4074f1d387491d20161058015e057415b0568158055c1560554153054813904e013504d013204c412f04b412c04a8129049c124048c120047c11d047011a04601170454114044810304040fe03f40fb03dc0f503c80f103bc0d203400cf03300ca02ec0b902d80b502cc0af02b40aa02a40a70228088021c084020800d00300090018002
def ridgeSupport131_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport131_code
def ridgeSupport131_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport131_code
def ridgeSupport131_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport131_code
def ridgeSupport131_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport131_code
def ridgeSupport131_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport131_code
def ridgeSupport131_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport131_code
def ridgeSupport131_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport131_code
def ridgeSupport131_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport131_code
def ridgeSupport131_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport131_code
def ridgeSupport131_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport131_code
def ridgeSupport131_suffix_009 : List Nat := []
def ridgeSupport131_suffix_008 : List Nat := ridgeSupport131_008 ++ ridgeSupport131_suffix_009
def ridgeSupport131_suffix_007 : List Nat := ridgeSupport131_007 ++ ridgeSupport131_suffix_008
def ridgeSupport131_suffix_006 : List Nat := ridgeSupport131_006 ++ ridgeSupport131_suffix_007
def ridgeSupport131_suffix_005 : List Nat := ridgeSupport131_005 ++ ridgeSupport131_suffix_006
def ridgeSupport131_suffix_004 : List Nat := ridgeSupport131_004 ++ ridgeSupport131_suffix_005
def ridgeSupport131_suffix_003 : List Nat := ridgeSupport131_003 ++ ridgeSupport131_suffix_004
def ridgeSupport131_suffix_002 : List Nat := ridgeSupport131_002 ++ ridgeSupport131_suffix_003
def ridgeSupport131_suffix_001 : List Nat := ridgeSupport131_001 ++ ridgeSupport131_suffix_002
def ridgeSupport131_suffix_000 : List Nat := ridgeSupport131_000 ++ ridgeSupport131_suffix_001
theorem ridgeSupport131_source : candidateSupports 131 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport131_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
