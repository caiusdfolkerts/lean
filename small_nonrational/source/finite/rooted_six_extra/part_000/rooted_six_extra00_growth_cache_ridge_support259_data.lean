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
def ridgeSupport259_000 : List Nat := [3,7,10,12,14,142,144,147,148,150,166,168,171,172,174,191,193,194,197,199,214,216,219,220,222,238,240,243,244,246,263,265]
def ridgeSupport259_001 : List Nat := [266,269,271,274,275,277,278,281,282,283,285,286,288,293,294,316,318,319,321,322,324,326,327,329,330,333,334,337,339,340,342,343]
def ridgeSupport259_002 : List Nat := [345,347,348,350,351,354,355,1866,1867,1872,1873,1876,1877,1878,1879,1880,1881,1886,1887,1890,1891,1896,1897,1900,1901,1902,1903,1904,1905,1910,1911,1924]
def ridgeSupport259_003 : List Nat := [1925,1926,1927,1928,1929,1948,1949,1950,1951,1952,1953,1972,1973,1974,1975,1976,1977,1996,1997,1998,1999,2000,2001,2020,2021,2022,2023,2024,2025,2044,2045,2046]
def ridgeSupport259_004 : List Nat := [2047,2048,2049,2057,2060,2063,2066,2068,2069,2070,2071,2072,2073,2074,2076,2588,2589,2600,2601,2624,2625,2636,2637,2644,2646,2650,2652,2730,2731,2742,2743,2766]
def ridgeSupport259_005 : List Nat := [2767,2778,2779,2789,2792,2795,2798,2802,2803,2814,2815,2838,2839,2850,2851,2861,2864,2867,2870,3356,3357,3368,3369,3392,3393,3404,3405,3412,3414,3418,3420,3498]
def ridgeSupport259_006 : List Nat := [3499,3510,3511,3534,3535,3546,3547,3557,3560,3563,3566,3570,3571,3582,3583,3606,3607,3618,3619,3629,3632,3635,3638,7060,7061,7062,7063,7064,7065,7684,7685,7686]
def ridgeSupport259_007 : List Nat := [7687,7688,7689,7697,7700,7703,7705,7706,7707,7709,7712,7715,7717,7718,7719,7822,7824,7828,7830,7859,7862,7865,7868,7877,7880,7883,7886,7990,7992,7996,7998,8027]
def ridgeSupport259_008 : List Nat := [8030,8033,8036,8045,8048,8051,8054]
def ridgeSupport259_code : Nat := 0x1f767dcdf707db5f647d85f5e7d6df3e7cf1f387cd9ece7b2dec87b15ebc7ae5eb67acde967a51e907a39e277899e25788de207875e1b7869e19785de147845e097821e077819e057811b996e61b976e59b956e50e3638cce3038b4e233888e173858dff37f8df337c8dee37acde83794ddb3768dcf3738db736d8dab36a8d5c3568d563550d4d3530d413500d2934a0d1d3470b362cccb302cb4b232c88b172c58aff2bf8af32bc8aee2bacae82b94adb2b68acf2b38ab72ad8aab2aa8a5c2968a562950a4d2930a412900a2928a0a1d287081c2068819206081720588152050812203c80c202480120007ff1ff87fd1ff07e91fa07e71f987e51f907d11f407cf1f387cd1f307b91ee07b71ed87b51ed07a11e8079f1e7879d1e707891e207871e187851e107771dd87711dc076f1db876d1db07691da07631d8875f1d787591d607571d587551d507511d4074b1d28163058815f057815c056c159055c1560550153054414e053414a05241470518144050814104fc13e04f01260494120047811d046c11a04641160454113044810f043410a042410703d80f403cc0f003b80de03700db03600d6031c0c503080c102fc0ae02b00ab02a00a60258094024c090023800e003000a001c003
def ridgeSupport259_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport259_code
def ridgeSupport259_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport259_code
def ridgeSupport259_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport259_code
def ridgeSupport259_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport259_code
def ridgeSupport259_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport259_code
def ridgeSupport259_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport259_code
def ridgeSupport259_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport259_code
def ridgeSupport259_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport259_code
def ridgeSupport259_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport259_code
def ridgeSupport259_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport259_code
def ridgeSupport259_suffix_009 : List Nat := []
def ridgeSupport259_suffix_008 : List Nat := ridgeSupport259_008 ++ ridgeSupport259_suffix_009
def ridgeSupport259_suffix_007 : List Nat := ridgeSupport259_007 ++ ridgeSupport259_suffix_008
def ridgeSupport259_suffix_006 : List Nat := ridgeSupport259_006 ++ ridgeSupport259_suffix_007
def ridgeSupport259_suffix_005 : List Nat := ridgeSupport259_005 ++ ridgeSupport259_suffix_006
def ridgeSupport259_suffix_004 : List Nat := ridgeSupport259_004 ++ ridgeSupport259_suffix_005
def ridgeSupport259_suffix_003 : List Nat := ridgeSupport259_003 ++ ridgeSupport259_suffix_004
def ridgeSupport259_suffix_002 : List Nat := ridgeSupport259_002 ++ ridgeSupport259_suffix_003
def ridgeSupport259_suffix_001 : List Nat := ridgeSupport259_001 ++ ridgeSupport259_suffix_002
def ridgeSupport259_suffix_000 : List Nat := ridgeSupport259_000 ++ ridgeSupport259_suffix_001
theorem ridgeSupport259_source : candidateSupports 259 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport259_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
