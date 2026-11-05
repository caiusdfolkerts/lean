module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport834_000 : List Nat := [311,312,313,735,736,737,823,824,825,907,908,909,953,954,955,1632,1633,1634,1635,1636,1637,1728,1729,1730,1731,1732,1733,1824,1825,1826,1827,1828]
def ridgeSupport834_001 : List Nat := [1829,2184,2185,2186,2187,2188,2189,2232,2233,2234,2235,2236,2237,2376,2377,2378,2379,2380,2381,2634,2635,2636,2637,2638,2639,2664,2665,2666,2667,2668,2669,3144]
def ridgeSupport834_002 : List Nat := [3145,3146,3147,3148,3149,3192,3193,3194,3195,3196,3197,3336,3337,3338,3339,3340,3341,3594,3595,3596,3597,3598,3599,3624,3625,3626,3627,3628,3629,4536,4537,4538]
def ridgeSupport834_003 : List Nat := [4539,4540,4541,4584,4585,4586,4587,4588,4589,4728,4729,4730,4731,4732,4733,5262,5263,5264,5265,5266,5267,5274,5275,5276,5277,5278,5279,7170,7171,7184,7185,7190]
def ridgeSupport834_004 : List Nat := [7191,7197,7199,7207,7210,7213,7216,7218,7219,7232,7233,7238,7239,7317,7319,7327,7330,7333,7336,7365,7367,7375,7378,7381,7384,7653,7655,7663,7666,7669,7672,7674]
def ridgeSupport834_005 : List Nat := [7675,7688,7689,7694,7695,7722,7723,7736,7737,7742,7743,7821,7823,7831,7834,7837,7840,7848,7849,7850,7851,7852,7853,8070,8071,8072,8073,8074,8075,8100,8101,8102]
def ridgeSupport834_006 : List Nat := [8103,8104,8105,8421,8423,8431,8434,8437,8440,8442,8443,8456,8457,8462,8463,8490,8491,8504,8505,8510,8511,8589,8591,8599,8602,8605,8608,8616,8617,8618,8619,8620]
def ridgeSupport834_007 : List Nat := [8621,8838,8839,8840,8841,8842,8843,8868,8869,8870,8871,8872,8873,9477,9479,9487,9490,9493,9496,9498,9499,9512,9513,9518,9519,9546,9547,9560,9561,9566,9567,9645]
def ridgeSupport834_008 : List Nat := [9647,9655,9658,9661,9664,9672,9673,9674,9675,9676,9677,10146,10147,10148,10149,10150,10151,10158,10159,10160,10161,10162,10163,11649,11651,11656,11709,11711,11719,11722,11725,11728]
def ridgeSupport834_009 : List Nat := [11901,11903,11908,11997,11999,12007,12010,12013,12016,12174,12175,12176,12177,12178,12179,12381,12383,12388,12477,12479,12487,12490,12493,12496,12654,12655,12656,12657,12658,12659,13077,13079]
def ridgeSupport834_010 : List Nat := [13084,13173,13175,13183,13186,13189,13192,13494,13495,13496,13497,13498,13499,14682,14683,14696,14697,14702,14703,14756,14758,14766,14771,14772,14777,14852,14854,14862,14867,14868,14873,14972]
def ridgeSupport834_011 : List Nat := [14974,14982,14987,14988,14993]
def ridgeSupport834_code : Nat := 0x3a91ea33a8bea1ba7ee9f3a19e853a13e83ba06e8139b9e6d39b3e6bb9a6e69396fe5bb969e5a395be56b4bbd2eb4b9d2e34b7d2db388ce17382cdff377cdd731ccc5f315c5cf172c5c7170c5bf16ec3430cdc32b0c7c2ff0bdc19305fc176f93be4af91be42f8fbe3aef0bbb6eeabb9eedfbb76e84b9fee7db742dcdb72adc7b6fedbdb622d83b6067b39eca7b19ec27af9eba7a79e9a7a59e927a39e8a5cd97325cb972a5c997225c096f65ba96de5af96b655f957a559956254b952a52f94ba52994a251b946a5189456512943e50794162a98aa22a78a9a2a58a9228b8a2a2898a222878a1a1ad86b21ab86aa1a986a21a0867619a865e18f863613f84fa13984e212b84aa10f843a10984220fb83ea0f883d60f283be0e78395fa97ea1fa77e99fa57e91f8b7e29f897e21f877e19ead7ab1eab7aa9ea97aa1ea07a75e9a7a5de8f7a35e3f78f9e3978e1e2b78a9e0f7839e097821dfb77e9df877d5df277bdde77795cd87355cd2733dcc77315ca87295ca2727dc977255c477119c417101c3370c9c3070b5c2a709dc1f7075c177059c117041c03700949f527949d527149b52694935249491524148f523927d49f127b49e927949e11ed47b11eb47a91e947a11bd46f11bb46e91b946e0e2d38b0e2b38a8e2938a0e0f3838e0d3830e0b3828d0d3430d0b3428d093420c7d31f0c7b31e8c7931e0c4d3130c4b3128c493120a6d29b0a6b29a8a6929a0a4f2938a4d2930a4b292894d253094b252894925208bd22f08bb22e88b922e088d223088b222888922207251c907231c887211c806c51b106c31b086c11b006651990663198866119803bb0ee83b90e3438c0e2c3390ce03370b842e00b7c13904e0137
def ridgeSupport834_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport834_code
def ridgeSupport834_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport834_code
def ridgeSupport834_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport834_code
def ridgeSupport834_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport834_code
def ridgeSupport834_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport834_code
def ridgeSupport834_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport834_code
def ridgeSupport834_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport834_code
def ridgeSupport834_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport834_code
def ridgeSupport834_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport834_code
def ridgeSupport834_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport834_code
def ridgeSupport834_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport834_code
def ridgeSupport834_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport834_code
def ridgeSupport834_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport834_code
def ridgeSupport834_suffix_012 : List Nat := []
def ridgeSupport834_suffix_011 : List Nat := ridgeSupport834_011 ++ ridgeSupport834_suffix_012
def ridgeSupport834_suffix_010 : List Nat := ridgeSupport834_010 ++ ridgeSupport834_suffix_011
def ridgeSupport834_suffix_009 : List Nat := ridgeSupport834_009 ++ ridgeSupport834_suffix_010
def ridgeSupport834_suffix_008 : List Nat := ridgeSupport834_008 ++ ridgeSupport834_suffix_009
def ridgeSupport834_suffix_007 : List Nat := ridgeSupport834_007 ++ ridgeSupport834_suffix_008
def ridgeSupport834_suffix_006 : List Nat := ridgeSupport834_006 ++ ridgeSupport834_suffix_007
def ridgeSupport834_suffix_005 : List Nat := ridgeSupport834_005 ++ ridgeSupport834_suffix_006
def ridgeSupport834_suffix_004 : List Nat := ridgeSupport834_004 ++ ridgeSupport834_suffix_005
def ridgeSupport834_suffix_003 : List Nat := ridgeSupport834_003 ++ ridgeSupport834_suffix_004
def ridgeSupport834_suffix_002 : List Nat := ridgeSupport834_002 ++ ridgeSupport834_suffix_003
def ridgeSupport834_suffix_001 : List Nat := ridgeSupport834_001 ++ ridgeSupport834_suffix_002
def ridgeSupport834_suffix_000 : List Nat := ridgeSupport834_000 ++ ridgeSupport834_suffix_001
theorem ridgeSupport834_source : candidateRows 834 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport834_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
