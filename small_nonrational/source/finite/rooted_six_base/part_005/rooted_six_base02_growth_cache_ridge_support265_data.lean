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
def ridgeSupport265_000 : List Nat := [7,22,24,26,186,189,190,193,196,210,213,214,217,220,235,236,239,240,245,332,418,419,421,422,425,426,427,429,430,432,437,438]
def ridgeSupport265_001 : List Nat := [460,462,463,465,466,468,470,471,473,474,477,478,481,483,484,486,487,489,491,492,494,495,498,499,2398,2399,2404,2405,2408,2409,2410,2411]
def ridgeSupport265_002 : List Nat := [2412,2413,2418,2419,2422,2423,2428,2429,2432,2433,2434,2435,2436,2437,2442,2443,2456,2457,2458,2459,2460,2461,2480,2481,2482,2483,2484,2485,2504,2505,2506,2507]
def ridgeSupport265_003 : List Nat := [2508,2509,2528,2529,2530,2531,2532,2533,2552,2553,2554,2555,2556,2557,2576,2577,2578,2579,2580,2581,2589,2592,2595,2598,2600,2601,2602,2603,2604,2605,2606,2608]
def ridgeSupport265_004 : List Nat := [2886,2887,2904,2905,2922,2923,2924,2926,2930,2932,2940,2941,3028,3029,3046,3047,3064,3065,3069,3072,3075,3078,3082,3083,3100,3101,3118,3119,3136,3137,3141,3144]
def ridgeSupport265_005 : List Nat := [3147,3150,3154,3155,3661,3663,3666,3669,3671,3672,3693,3695,3698,3701,3703,3704,3724,3726,3731,3732,3734,3737,5746,5747,5750,5751,5754,5755,5758,5759,5762,5763]
def ridgeSupport265_006 : List Nat := [5766,5767,5780,5781,5782,5783,5784,5785,5804,5805,5806,5807,5808,5809,5817,5820,5823,5826,5828,5829,5830,5831,5832,5833,5834,5836,5841,5844,5847,5850,5852,5853]
def ridgeSupport265_007 : List Nat := [5854,5855,5856,5857,5858,5860,5864,5866,5867,5869,5874,5875,6018,6019,6020,6022,6026,6028,6036,6037,6045,6047,6054,6055,6056,6058,6124,6125,6129,6132,6135,6138]
def ridgeSupport265_008 : List Nat := [6142,6143,6152,6157,6160,6161,6165,6168,6178,6179,6183,6186,6189,6192,6196,6197,6206,6211,6214,6215,6219,6222,6493,6494,6501,6502,6508,6511,7426,7427,7430,7431]
def ridgeSupport265_009 : List Nat := [7434,7435,7449,7451,7460,7465,7466,7471,7724,7725,7726,7727,7728,7729,7887,7895,7902]
def ridgeSupport265_code : Nat := 0x1edef6bfb3fc63e30f17f8bbc5be2ce97f4aba53d24e8df467a17d0ae83f41ba07d02cb7e5b32cd965caf657709d84bc23e11b08783ec1ae0d306182dc15609f047822c0c6057023810c06e022fff7febfd5fdefe97f1bf6dfb2f557a8bd3de9af3f79dbcade52f1978abc35e12f07782b79dbcaddb6ebb755ba2dc96e2b70db82dbf6deb6edb72db56d7b6a5b46d996cab64db22d8f6c6b62db12d856bfb5e5ae6d636b0b57dabad5b6acb4cda62d2f696b4ada52d0f686b41da0acff67eb3dd9eacef676b39d9c9d32e9674a3a4dd1ce8c73c39ddceae72737b9b5cb0e5772ab949c9ee4d629b14989cc4b6243115882c40617b0b983ac1c605b02980cc036002ff57f2bf85f3af997aabd45beadf16e8b725b72db16d6b6a5acad6168eb4651828b945aa2c515a8a9452a28513288d440a1d50aa851426a12508a8413fa9fc4fda7e93f29f84f2a7913c69e24f0a78139a9cc4e5a7293929c84daa6d13669b24d8a6c133a99c4cda6693329984c5a62930a9844c1a6093029804bea5f12ee9764b9a5c92da96c4b5a5a92d29684b2a5912be95e0f987c83de1ee0f607ac3d21e70f307903c61e10ef07743b41d90eb87583a81d20e8873c39c1cc0db06d43601ae0d686ac3541a90d306943461a20a603d41e00ef07603ac1b80d906b03541a40c406082f817a0ba00d006002c007
def ridgeSupport265_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport265_code
def ridgeSupport265_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport265_code
def ridgeSupport265_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport265_code
def ridgeSupport265_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport265_code
def ridgeSupport265_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport265_code
def ridgeSupport265_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport265_code
def ridgeSupport265_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport265_code
def ridgeSupport265_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport265_code
def ridgeSupport265_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport265_code
def ridgeSupport265_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport265_code
def ridgeSupport265_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport265_code
def ridgeSupport265_suffix_010 : List Nat := []
def ridgeSupport265_suffix_009 : List Nat := ridgeSupport265_009 ++ ridgeSupport265_suffix_010
def ridgeSupport265_suffix_008 : List Nat := ridgeSupport265_008 ++ ridgeSupport265_suffix_009
def ridgeSupport265_suffix_007 : List Nat := ridgeSupport265_007 ++ ridgeSupport265_suffix_008
def ridgeSupport265_suffix_006 : List Nat := ridgeSupport265_006 ++ ridgeSupport265_suffix_007
def ridgeSupport265_suffix_005 : List Nat := ridgeSupport265_005 ++ ridgeSupport265_suffix_006
def ridgeSupport265_suffix_004 : List Nat := ridgeSupport265_004 ++ ridgeSupport265_suffix_005
def ridgeSupport265_suffix_003 : List Nat := ridgeSupport265_003 ++ ridgeSupport265_suffix_004
def ridgeSupport265_suffix_002 : List Nat := ridgeSupport265_002 ++ ridgeSupport265_suffix_003
def ridgeSupport265_suffix_001 : List Nat := ridgeSupport265_001 ++ ridgeSupport265_suffix_002
def ridgeSupport265_suffix_000 : List Nat := ridgeSupport265_000 ++ ridgeSupport265_suffix_001
theorem ridgeSupport265_source : candidateSupports 265 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport265_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
