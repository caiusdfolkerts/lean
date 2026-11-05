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
def ridgeSupport705_000 : List Nat := [293,294,295,449,450,451,533,534,535,603,604,605,1662,1663,1664,1665,1666,1667,1710,1711,1712,1713,1714,1715,1854,1855,1856,1857,1858,1859,1926,1927]
def ridgeSupport705_001 : List Nat := [1928,1929,1930,1931,1974,1975,1976,1977,1978,1979,2118,2119,2120,2121,2122,2123,2538,2539,2540,2541,2542,2543,2550,2551,2552,2553,2554,2555,2886,2887,2888,2889]
def ridgeSupport705_002 : List Nat := [2890,2891,2934,2935,2936,2937,2938,2939,3078,3079,3080,3081,3082,3083,3498,3499,3500,3501,3502,3503,3510,3511,3512,3513,3514,3515,4194,4195,4196,4197,4198,4199]
def ridgeSupport705_003 : List Nat := [4206,4207,4208,4209,4210,4211,7171,7174,7177,7180,7188,7190,7196,7197,7202,7203,7216,7217,7244,7245,7250,7251,7264,7265,7339,7342,7345,7348,7356,7358,7374,7375]
def ridgeSupport705_004 : List Nat := [7376,7377,7378,7379,7411,7414,7417,7420,7428,7430,7436,7437,7442,7443,7456,7457,7484,7485,7490,7491,7504,7505,7579,7582,7585,7588,7596,7598,7614,7615,7616,7617]
def ridgeSupport705_005 : List Nat := [7618,7619,8010,8011,8012,8013,8014,8015,8022,8023,8024,8025,8026,8027,8179,8182,8185,8188,8196,8198,8204,8205,8210,8211,8224,8225,8252,8253,8258,8259,8272,8273]
def ridgeSupport705_006 : List Nat := [8347,8350,8353,8356,8364,8366,8382,8383,8384,8385,8386,8387,8778,8779,8780,8781,8782,8783,8790,8791,8792,8793,8794,8795,9306,9307,9308,9309,9310,9311,9318,9319]
def ridgeSupport705_007 : List Nat := [9320,9321,9322,9323,11635,11638,11642,11731,11734,11737,11740,11748,11750,11767,11770,11774,11863,11866,11869,11872,11880,11882,12132,12133,12134,12135,12136,12137,12247,12250,12254,12343]
def ridgeSupport705_008 : List Nat := [12346,12349,12352,12360,12362,12612,12613,12614,12615,12616,12617,12960,12961,12962,12963,12964,12965,14682,14687,14688,14693,14701,14703,14718,14723,14724,14729,14737,14739,14814,14819,14820]
def ridgeSupport705_009 : List Nat := [14825,14833,14835]
def ridgeSupport705_code : Nat := 0x39f3e7c79e9e7939e3e77b993e647989e613983e5fb96fe5b7965e58395fe56b2a5ca932a3ca8b2a1ca83149c523147c51b145c51304ac123040c0f703ac0defdebf6afd7bda6f68bd9ef66bd96f64b9aae68b982e5db96ae57b7fadfab7dede6b792ddcb766dd6b74ed7ab5dad7391ae46a91a6468919e466917e45e917645c916e45a896e25a8966258895e256893e24e893624c892e24a830e0c283060c082fe0be82ba0ac82920a1827a09b8146050810e04280f603c8086020804e012803600c801a0047ff1ff97fd9ff37d6df5a7d65f587d5df567d3df4e7d35f4c7d2df4a770ddc27705dc076fddbe76b9dac7691da17679d9b7545d50750dd4274f5d3c7485d20744dd127435d0c7419d0473f1cf973d9cf3734dcd27345cd0733dcce72f9cbc72d1cb172b9cab7185c60714dc527135c4c70c5c30708dc227075c1c7059c147031c097019c0341cd07241c507041bd06e419d0664195064418d06236ecdba36e4db836dcdb636bcdae36b4dac36acdaa302cc0a3024c08301cc062decb7a2de4b782ddcb762d2cb4a2d24b482d1cb4627ec9fa27e49f827dc9f627bc9ee27b49ec27ac9ea212c84a2124848211c8461eec7ba1ee47b81edc7b61e2c78a1e247881e1c7861d0c7421d047401cfc73e1acc6b21ac46b01abc6ae1a0c6821a0468019fc67e097425c096c2170858215070c1c207041270498125
def ridgeSupport705_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport705_code
def ridgeSupport705_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport705_code
def ridgeSupport705_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport705_code
def ridgeSupport705_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport705_code
def ridgeSupport705_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport705_code
def ridgeSupport705_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport705_code
def ridgeSupport705_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport705_code
def ridgeSupport705_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport705_code
def ridgeSupport705_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport705_code
def ridgeSupport705_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport705_code
def ridgeSupport705_rest_010 : Nat := PackedRawNatGrowth.drop 4074 ridgeSupport705_code
def ridgeSupport705_suffix_010 : List Nat := []
def ridgeSupport705_suffix_009 : List Nat := ridgeSupport705_009 ++ ridgeSupport705_suffix_010
def ridgeSupport705_suffix_008 : List Nat := ridgeSupport705_008 ++ ridgeSupport705_suffix_009
def ridgeSupport705_suffix_007 : List Nat := ridgeSupport705_007 ++ ridgeSupport705_suffix_008
def ridgeSupport705_suffix_006 : List Nat := ridgeSupport705_006 ++ ridgeSupport705_suffix_007
def ridgeSupport705_suffix_005 : List Nat := ridgeSupport705_005 ++ ridgeSupport705_suffix_006
def ridgeSupport705_suffix_004 : List Nat := ridgeSupport705_004 ++ ridgeSupport705_suffix_005
def ridgeSupport705_suffix_003 : List Nat := ridgeSupport705_003 ++ ridgeSupport705_suffix_004
def ridgeSupport705_suffix_002 : List Nat := ridgeSupport705_002 ++ ridgeSupport705_suffix_003
def ridgeSupport705_suffix_001 : List Nat := ridgeSupport705_001 ++ ridgeSupport705_suffix_002
def ridgeSupport705_suffix_000 : List Nat := ridgeSupport705_000 ++ ridgeSupport705_suffix_001
theorem ridgeSupport705_source : candidateRows 705 =
    (PackedRawNatGrowth.readList 14 291 ridgeSupport705_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
