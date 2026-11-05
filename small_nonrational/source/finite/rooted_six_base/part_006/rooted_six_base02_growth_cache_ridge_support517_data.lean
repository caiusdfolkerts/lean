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
def ridgeSupport517_000 : List Nat := [4,17,19,20,126,129,130,133,136,150,153,154,157,160,162,165,166,169,172,333,355,356,358,359,362,363,364,366,367,369,374,375]
def ridgeSupport517_001 : List Nat := [376,377,379,380,383,384,385,387,388,390,395,396,397,398,400,401,404,405,406,408,409,411,416,417,1632,1633,1638,1639,1644,1645,1646,1647]
def ridgeSupport517_002 : List Nat := [1648,1649,1650,1651,1656,1657,1662,1663,1668,1669,1670,1671,1672,1673,1674,1675,1694,1695,1696,1697,1698,1699,1718,1719,1720,1721,1722,1723,1742,1743,1744,1745]
def ridgeSupport517_003 : List Nat := [1746,1747,1766,1767,1768,1769,1770,1771,1790,1791,1792,1793,1794,1795,1814,1815,1816,1817,1818,1819,1820,1822,1826,1828,1832,1834,1838,1839,1840,1841,1842,1843]
def ridgeSupport517_004 : List Nat := [2190,2191,2208,2209,2226,2227,2228,2230,2234,2236,2244,2245,2262,2263,2280,2281,2298,2299,2300,2302,2306,2308,2316,2317,2334,2335,2352,2353,2370,2371,2372,2374]
def ridgeSupport517_005 : List Nat := [2378,2380,2388,2389,3677,3679,3681,3683,3686,3690,3709,3711,3713,3715,3718,3722,3725,3727,3729,3731,3734,3738,5268,5269,5272,5273,5274,5275,5280,5281,5284,5285]
def ridgeSupport517_006 : List Nat := [5286,5287,5306,5307,5308,5309,5310,5311,5330,5331,5332,5333,5334,5335,5336,5338,5342,5344,5348,5350,5354,5355,5356,5357,5358,5359,5360,5362,5366,5368,5372,5374]
def ridgeSupport517_007 : List Nat := [5378,5379,5380,5381,5382,5383,5385,5386,5388,5389,5391,5392,5592,5593,5594,5596,5600,5602,5610,5611,5619,5621,5628,5629,5630,5632,5646,5647,5648,5650,5654,5656]
def ridgeSupport517_008 : List Nat := [5664,5665,5673,5675,5682,5683,5684,5686,5700,5701,5702,5704,5708,5710,5718,5719,5727,5729,5736,5737,5738,5740,6497,6499,6505,6507,6509,6511,7380,7381,7384,7385]
def ridgeSupport517_009 : List Nat := [7386,7387,7407,7409,7413,7415,7419,7421,7634,7635,7636,7637,7638,7639,7889,7897,7901]
def ridgeSupport517_code : Nat := 0x1eddf6cfb47bafdd6eeaf753ba7dd2e7ef3ef9efcf5e78f3bf9b7cdae6cf3639abcd4cb7e5b72d7969cb1e586cd966ab34d9a2cc365fb2bd95ac9d64cb24591ac8b644b1b58d2c67632b15d8a6c43620b0c585ac25610b07d83ac015feafed7f2beb5f3af5d7aabc55e0aee576abb35d8a88543ea1b50ca855426a0f506a82d412a07502a7f53f29f14f6a7953c29df4eea76d3b29d74eaa7353929c14dea6d53629af4d6a6ad3529a74d2a5fd2fa97b4bca5dd2ea94f4a6a52d2929434a0a4dd26a933498a4ad251d34e96749ba45d1ee8d7453a19d06e8173fb9f5cd4e66731b985cbee5d4aaa55129894a4a32511286942498a4c123e91e486a43120890247f23f11f68fa474a3a11ae8d6462a3111788ba45b22d11668b2450a28111e88e3999cc8e627303979cb8e547283921c88e3c71c38d9c68e3271838b9c58e067023809c00dfe6fe3759ba8dd26e83739b98da66d23689b40d9e6ce35d9ae8d726b835b9ad8d466a23509a80d3e69e3459a28d126883439a18d0a68433f99f8cf267833999c8ce267033799b8cda66c3339998cc26600d086803361990cc065832a1940c8864031c18d0c6062c30c1840c1860430017f0be05ec2f21780bb85d82e216f0b705b02d616a0b385982c81630a682b01520a6052828814009d04d026412c088042820810207e00a004c022004
def ridgeSupport517_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport517_code
def ridgeSupport517_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport517_code
def ridgeSupport517_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport517_code
def ridgeSupport517_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport517_code
def ridgeSupport517_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport517_code
def ridgeSupport517_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport517_code
def ridgeSupport517_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport517_code
def ridgeSupport517_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport517_code
def ridgeSupport517_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport517_code
def ridgeSupport517_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport517_code
def ridgeSupport517_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport517_code
def ridgeSupport517_suffix_010 : List Nat := []
def ridgeSupport517_suffix_009 : List Nat := ridgeSupport517_009 ++ ridgeSupport517_suffix_010
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
    (PackedRawNatGrowth.readList 13 305 ridgeSupport517_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
