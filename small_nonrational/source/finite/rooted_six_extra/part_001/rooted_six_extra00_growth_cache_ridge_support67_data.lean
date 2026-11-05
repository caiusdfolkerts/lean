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
def ridgeSupport67_000 : List Nat := [1,5,9,10,11,131,133,134,137,139,143,145,146,149,151,155,157,158,161,163,203,205,206,209,211,215,217,218,221,223,227,229]
def ridgeSupport67_001 : List Nat := [230,233,235,275,276,278,279,280,281,283,284,286,287,289,290,296,297,299,300,301,302,304,305,307,308,310,311,317,318,320,321,322]
def ridgeSupport67_002 : List Nat := [323,325,326,328,329,331,332,1864,1865,1866,1867,1868,1869,1870,1871,1876,1877,1882,1883,1888,1889,1890,1891,1892,1893,1894,1895,1900,1901,1906,1907,1912]
def ridgeSupport67_003 : List Nat := [1913,1914,1915,1916,1917,1936,1937,1938,1939,1940,1941,1960,1961,1962,1963,1964,1965,1984,1985,1986,1987,1988,1989,2008,2009,2010,2011,2012,2013,2032,2033,2034]
def ridgeSupport67_004 : List Nat := [2035,2036,2037,2056,2057,2058,2059,2060,2061,2065,2067,2071,2073,2077,2079,2584,2585,2596,2597,2620,2621,2632,2633,2647,2649,2653,2655,2656,2657,2668,2669,2692]
def ridgeSupport67_005 : List Nat := [2693,2704,2705,2719,2721,2725,2727,2728,2729,2740,2741,2764,2765,2776,2777,2791,2793,2797,2799,3352,3353,3364,3365,3388,3389,3400,3401,3415,3417,3421,3423,3424]
def ridgeSupport67_006 : List Nat := [3425,3436,3437,3460,3461,3472,3473,3487,3489,3493,3495,3496,3497,3508,3509,3532,3533,3544,3545,3559,3561,3565,3567,7048,7049,7050,7051,7052,7053,7672,7673,7674]
def ridgeSupport67_007 : List Nat := [7675,7676,7677,7696,7697,7698,7699,7700,7701,7708,7709,7710,7711,7712,7713,7825,7827,7831,7833,7843,7845,7849,7851,7861,7863,7867,7869,7993,7995,7999,8001,8011]
def ridgeSupport67_008 : List Nat := [8013,8017,8019,8029,8031,8035,8037]
def ridgeSupport67_code : Nat := 0x1f657d8df5f7d75f537d45f4d7d2df417cfdf3b7ce5ebd7aedeb77ad5eab7aa5ea57a8de997a5de937a45e217881e1f7879e1d7871e157851e137849e117841dfd77f1dfb77e9df977e1b8d6e31b8b6e29b896e20def37b4de9379cdd93760dcd3730db536d0da936a0da73694da1367cd913640d853610d6d35b0d613580d5f3574d59355cd493520d3d34f0d253490d193460aef2bb4ae92b9cad92b60acd2b30ab52ad0aa92aa0aa72a94aa12a7ca912a40a852a10a6d29b0a612980a5f2974a59295ca492920a3d28f0a252890a19286081f2074819205c813204480d203080b202880920207f51fd07f31fc87f11fc07dd1f707db1f687d91f607c51f107c31f087c11f007ad1eb07ab1ea87a91ea07951e507931e487911e4077d1df077b1de87791de07731dc876d1db07671d987651d907631d887611d8075b1d687551d5074f1d3874d1d3074b1d287491d2014c052c149052014605141430508141050013e04f413704d813404cc13104c012e04b412c04ac12904a0122048411f047811c046c11904601170458114044c0eb03a40e603940e3037c0dd03680d9035c0d303440ce03340cb028c0a1027809d026c0970254092024408f022c0890218085020c00b00280090014001
def ridgeSupport67_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport67_code
def ridgeSupport67_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport67_code
def ridgeSupport67_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport67_code
def ridgeSupport67_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport67_code
def ridgeSupport67_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport67_code
def ridgeSupport67_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport67_code
def ridgeSupport67_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport67_code
def ridgeSupport67_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport67_code
def ridgeSupport67_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport67_code
def ridgeSupport67_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport67_code
def ridgeSupport67_suffix_009 : List Nat := []
def ridgeSupport67_suffix_008 : List Nat := ridgeSupport67_008 ++ ridgeSupport67_suffix_009
def ridgeSupport67_suffix_007 : List Nat := ridgeSupport67_007 ++ ridgeSupport67_suffix_008
def ridgeSupport67_suffix_006 : List Nat := ridgeSupport67_006 ++ ridgeSupport67_suffix_007
def ridgeSupport67_suffix_005 : List Nat := ridgeSupport67_005 ++ ridgeSupport67_suffix_006
def ridgeSupport67_suffix_004 : List Nat := ridgeSupport67_004 ++ ridgeSupport67_suffix_005
def ridgeSupport67_suffix_003 : List Nat := ridgeSupport67_003 ++ ridgeSupport67_suffix_004
def ridgeSupport67_suffix_002 : List Nat := ridgeSupport67_002 ++ ridgeSupport67_suffix_003
def ridgeSupport67_suffix_001 : List Nat := ridgeSupport67_001 ++ ridgeSupport67_suffix_002
def ridgeSupport67_suffix_000 : List Nat := ridgeSupport67_000 ++ ridgeSupport67_suffix_001
theorem ridgeSupport67_source : candidateSupports 67 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport67_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
