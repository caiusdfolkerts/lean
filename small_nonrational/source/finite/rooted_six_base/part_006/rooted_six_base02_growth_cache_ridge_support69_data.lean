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
def ridgeSupport69_000 : List Nat := [1,15,16,17,103,104,107,108,113,115,116,119,120,125,127,128,131,132,137,330,335,336,338,339,340,341,343,344,346,347,349,350]
def ridgeSupport69_001 : List Nat := [356,357,359,360,361,362,364,365,367,368,370,371,377,378,380,381,382,383,385,386,388,389,391,392,1628,1629,1630,1631,1632,1633,1634,1635]
def ridgeSupport69_002 : List Nat := [1640,1641,1646,1647,1652,1653,1654,1655,1656,1657,1658,1659,1664,1665,1670,1671,1676,1677,1678,1679,1680,1681,1700,1701,1702,1703,1704,1705,1724,1725,1726,1727]
def ridgeSupport69_003 : List Nat := [1728,1729,1748,1749,1750,1751,1752,1753,1772,1773,1774,1775,1776,1777,1796,1797,1798,1799,1800,1801,1820,1821,1822,1823,1824,1825,1829,1831,1835,1837,1841,1843]
def ridgeSupport69_004 : List Nat := [2114,2115,2132,2133,2150,2151,2159,2161,2165,2167,2168,2169,2186,2187,2204,2205,2222,2223,2231,2233,2237,2239,2240,2241,2258,2259,2276,2277,2294,2295,2303,2305]
def ridgeSupport69_005 : List Nat := [2309,2311,2312,2313,3644,3646,3648,3650,3655,3659,3660,3662,3664,3666,3671,3675,3676,3678,3680,3682,3687,3691,5264,5265,5266,5267,5268,5269,5276,5277,5278,5279]
def ridgeSupport69_006 : List Nat := [5280,5281,5288,5289,5290,5291,5292,5293,5312,5313,5314,5315,5316,5317,5336,5337,5338,5339,5340,5341,5345,5347,5351,5353,5357,5359,5360,5361,5362,5363,5364,5365]
def ridgeSupport69_007 : List Nat := [5369,5371,5375,5377,5381,5383,5387,5388,5390,5391,5393,5394,5534,5535,5543,5545,5549,5551,5552,5553,5566,5568,5570,5571,5579,5581,5588,5589,5597,5599,5603,5605]
def ridgeSupport69_008 : List Nat := [5606,5607,5620,5622,5624,5625,5633,5635,5642,5643,5651,5653,5657,5659,5660,5661,5674,5676,5678,5679,5687,5689,6488,6490,6492,6494,6496,6498,7376,7377,7378,7379]
def ridgeSupport69_009 : List Nat := [7380,7381,7402,7404,7408,7410,7414,7416,7616,7617,7618,7619,7620,7621,7880,7884,7888]
def ridgeSupport69_code : Nat := 0x1ed0f667b23b8bdc4ee1f70bb83dc0e7c73db9e5cf0e7673ab9abcd4e69f34b9a3cd0cb165832bd95ccad6562c73637b17d8bac5962ab0ed872c37619b0ad84ec1760ab01d806bf35f8afb57d2bcf5e6af2d78ebbf5ddaead752b9b5cbae1d70ab815bead8d6c2b5f5adad4d69eb3f59ea895446a1f50ea86542ea0f505a80d3fe9f74f9a7ad3d29e74f2a78d3c29df4eda74d39e9c74e1a6ed3729b74daa6cd36298b4c4a61d30a9834c0a56d2b29574aaa54d2a29434a0a4fd27a93b49ca4ad252927492a48d241cd6e677313981cbce5c72db95dca4e507273931c96e477213901c7ce3c484a42120e905480a3fd1ee8f6472a3911a68d2460a30117e8bd45ca2dd15e8ae44ea27111688a43ca1e10ee875438a1bd0ce86642aa1510868423999cc4e5a72b3939c94e4272038f9c78e3a71c3849c20e0e7063829c10de26f03779bb8dda6ec36c9b60dae6d636a9b50d826c035f9af8d7a6bc3549aa0d4e6a63529a90d226903479a38d1a68c3439a18d0268033d99e8cf267833b99d8cea67433799b8cd26683319988cc266032f9978cba65c0c4061c30a1840c106042fe17e0be85f02f41790b985c82e016f0b685b02d41690b4059c2ca1640af05742b615a0ac055c2aa1540a985482a014f0a5022410808304001fc0fa07803b81d00e607103601ac0d0067008804001e001
def ridgeSupport69_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport69_code
def ridgeSupport69_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport69_code
def ridgeSupport69_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport69_code
def ridgeSupport69_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport69_code
def ridgeSupport69_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport69_code
def ridgeSupport69_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport69_code
def ridgeSupport69_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport69_code
def ridgeSupport69_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport69_code
def ridgeSupport69_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport69_code
def ridgeSupport69_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport69_code
def ridgeSupport69_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport69_code
def ridgeSupport69_suffix_010 : List Nat := []
def ridgeSupport69_suffix_009 : List Nat := ridgeSupport69_009 ++ ridgeSupport69_suffix_010
def ridgeSupport69_suffix_008 : List Nat := ridgeSupport69_008 ++ ridgeSupport69_suffix_009
def ridgeSupport69_suffix_007 : List Nat := ridgeSupport69_007 ++ ridgeSupport69_suffix_008
def ridgeSupport69_suffix_006 : List Nat := ridgeSupport69_006 ++ ridgeSupport69_suffix_007
def ridgeSupport69_suffix_005 : List Nat := ridgeSupport69_005 ++ ridgeSupport69_suffix_006
def ridgeSupport69_suffix_004 : List Nat := ridgeSupport69_004 ++ ridgeSupport69_suffix_005
def ridgeSupport69_suffix_003 : List Nat := ridgeSupport69_003 ++ ridgeSupport69_suffix_004
def ridgeSupport69_suffix_002 : List Nat := ridgeSupport69_002 ++ ridgeSupport69_suffix_003
def ridgeSupport69_suffix_001 : List Nat := ridgeSupport69_001 ++ ridgeSupport69_suffix_002
def ridgeSupport69_suffix_000 : List Nat := ridgeSupport69_000 ++ ridgeSupport69_suffix_001
theorem ridgeSupport69_source : candidateSupports 69 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport69_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
