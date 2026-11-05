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
def ridgeSupport322_000 : List Nat := [10,32,42,48,53,55,114,115,118,119,122,123,186,187,190,191,194,195,246,248,250,252,254,259,260,262,265,288,289,293,295,296]
def ridgeSupport322_001 : List Nat := [300,302,303,305,532,534,536,537,539,541,542,546,551,575,576,577,580,581,582,584,589,591,629,630,631,632,633,634,688,690,692,693]
def ridgeSupport322_002 : List Nat := [695,697,698,702,707,731,732,733,736,737,738,740,745,747,772,774,776,777,779,781,782,786,791,815,816,817,820,821,822,824,829,831]
def ridgeSupport322_003 : List Nat := [856,858,859,861,862,864,866,867,869,870,874,875,1395,1397,1406,1411,1462,1463,1472,1473,1485,1488,1494,1495,1499,1501,1504,1505,1510,1511,1520,1521]
def ridgeSupport322_004 : List Nat := [1558,1559,1563,1565,1568,1569,1574,1579,1590,1591,1600,1601,1614,1615,1624,1625,1899,1901,1910,1915,1918,1919,1928,1929,1966,1967,1976,1977,1989,1992,1998,1999]
def ridgeSupport322_005 : List Nat := [2003,2005,2008,2009,2014,2015,2019,2021,2024,2025,2030,2035,2062,2063,2072,2073,2086,2087,2096,2097,2108,2113,2138,2143,2152,2153,2170,2171,2253,2255,2283,2285]
def ridgeSupport322_006 : List Nat := [2298,2299,2316,2317,2667,2669,2678,2683,2686,2687,2696,2697,2734,2735,2744,2745,2757,2760,2766,2767,2771,2773,2776,2777,2782,2783,2787,2789,2792,2793,2798,2803]
def ridgeSupport322_007 : List Nat := [2830,2831,2840,2841,2854,2855,2864,2865,2876,2881,2906,2911,2920,2921,2938,2939,3021,3023,3051,3053,3066,3067,3084,3085,3771,3773,3782,3787,3790,3791,3800,3801]
def ridgeSupport322_008 : List Nat := [3838,3839,3848,3849,3861,3864,3870,3871,3875,3877,3880,3881,3886,3887,3891,3893,3896,3897,3902,3907,3934,3935,3944,3945,3958,3959,3968,3969,4232,4237,4244,4249]
def ridgeSupport322_009 : List Nat := [4276,4277,4288,4289,4377,4379,4389,4391,4422,4423,4434,4435,4770,4771,4778,4779,5133,5136,5139,5143,5156,5161,5162,5166,5168,5173,5181,5183,5204,5209,5210,5214]
def ridgeSupport322_010 : List Nat := [5216,5221,5229,5231,5264,5269,5270,5274,5289,5292,5300,5302,5380,5381,5446,5447,5542,5543,5698,5699,5854,5855,5864,5865,5878,5879,5882,5884,5885,5886,5949,5952]
def ridgeSupport322_011 : List Nat := [5963,5965,5986,5987,5990,5992,5993,5994,6003,6004,6005,6006,6038,6040,6042,6043,6117,6120,6131,6133,6154,6155,6158,6160,6161,6162,6171,6172,6173,6174,6206,6208]
def ridgeSupport322_012 : List Nat := [6210,6211,6333,6336,6347,6349,6370,6371,6374,6376,6377,6378,6441,6442,6443,6444,6476,6478,6480,6481]
def ridgeSupport322_code : Nat := 0xca8e54329d94cc9664af255929c7563a71d18e6c71e38b19b8cbc6062f7087842c2060fb03d81dc0e606f025811c08603b01780abfadfcefd17e5bcdde6af31796bbb5dd6ee9773bb55da6ed1766bb1dd8ae9b74bba05cf6dfd6fdb7e5beadef6f6b74dba2dbf6deb21d90ab4f5a6aa3d51aa0b504a5b52d29594a9a4d525a92b490a37d1b68cb460a2f516a8b3454a1fd0f686b430a1750aa853424a0bd04e82140d955caaa5472a28a9c54a28f146893c496237119860c30216b0b484cc25211b0887c0be01eeef767b4bda1ebef5e7a1bcf9e72f3879abccde5ef2e794bca1e4af2378fbc79e30f15784bc21dfeefe76cbb61d9eece765bb19d7aebb606b0317f6bfa5f6afad79ebcd5bdade96d2b685afad69682b3c598acc164eb2658cac6161eb0e579abb95d2ae8572ab8d5beade56cab615aaad3567ab39590ac555caae155eaae544aa214fea7e53da9d94daa6b486a4311f68fa476a3ad19e8cd43da1e90d286842fa16908283c418a0c104e82640ca06101e80e3f99fb8fd27e83f29f8cfbe7de3ec9f60faa7d33e79f38f907c53dc9ee0f5e7ae3c49e20efe77e3bd9dd8eda76b32c9960c9e64e3209900c6e6363159898c4262030e986cc2e6162f897c0bce5e62f09780bba5db2eb9758ba05cd2e09700b6e5b62c195f8aea5731b58da86cc3651b18d886c035e1ae8d6c6b435819f8cf467033619a8cd06623301978c5c62430e1868c2c6123081830c105d62e91720b885c22e016e8b705b62c315f0ae85722b715a8ad05642b013d09e44f027713b09d449e24d124091848a244120890047e227111087843a21b10c886042c21409884bc25c12c094049c24a121090042420c10408183f81f80fa07c03d81860c205f82f81760ba03d81e80ee07603981c806e03501800a804000a
def ridgeSupport322_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport322_code
def ridgeSupport322_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport322_code
def ridgeSupport322_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport322_code
def ridgeSupport322_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport322_code
def ridgeSupport322_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport322_code
def ridgeSupport322_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport322_code
def ridgeSupport322_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport322_code
def ridgeSupport322_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport322_code
def ridgeSupport322_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport322_code
def ridgeSupport322_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport322_code
def ridgeSupport322_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport322_code
def ridgeSupport322_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport322_code
def ridgeSupport322_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport322_code
def ridgeSupport322_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport322_code
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
    (PackedRawNatGrowth.readList 13 404 ridgeSupport322_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
