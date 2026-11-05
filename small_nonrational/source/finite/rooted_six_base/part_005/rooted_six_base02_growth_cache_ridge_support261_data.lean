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
def ridgeSupport261_000 : List Nat := [3,16,18,20,114,117,118,121,124,138,141,142,145,148,163,164,167,168,173,332,334,335,337,338,341,342,343,345,346,348,353,354]
def ridgeSupport261_001 : List Nat := [376,378,379,381,382,384,386,387,389,390,393,394,397,399,400,402,403,405,407,408,410,411,414,415,1630,1631,1636,1637,1640,1641,1642,1643]
def ridgeSupport261_002 : List Nat := [1644,1645,1650,1651,1654,1655,1660,1661,1664,1665,1666,1667,1668,1669,1674,1675,1688,1689,1690,1691,1692,1693,1712,1713,1714,1715,1716,1717,1736,1737,1738,1739]
def ridgeSupport261_003 : List Nat := [1740,1741,1760,1761,1762,1763,1764,1765,1784,1785,1786,1787,1788,1789,1808,1809,1810,1811,1812,1813,1821,1824,1827,1830,1832,1833,1834,1835,1836,1837,1838,1840]
def ridgeSupport261_004 : List Nat := [2118,2119,2136,2137,2154,2155,2156,2158,2162,2164,2172,2173,2260,2261,2278,2279,2296,2297,2301,2304,2307,2310,2314,2315,2332,2333,2350,2351,2368,2369,2373,2376]
def ridgeSupport261_005 : List Nat := [2379,2382,2386,2387,3661,3663,3665,3667,3670,3674,3693,3695,3697,3699,3702,3706,3724,3726,3728,3730,3735,3739,5266,5267,5270,5271,5274,5275,5278,5279,5282,5283]
def ridgeSupport261_006 : List Nat := [5286,5287,5300,5301,5302,5303,5304,5305,5324,5325,5326,5327,5328,5329,5337,5340,5343,5346,5348,5349,5350,5351,5352,5353,5354,5356,5361,5364,5367,5370,5372,5373]
def ridgeSupport261_007 : List Nat := [5374,5375,5376,5377,5378,5380,5384,5386,5387,5389,5394,5395,5538,5539,5540,5542,5546,5548,5556,5557,5565,5567,5574,5575,5576,5578,5644,5645,5649,5652,5655,5658]
def ridgeSupport261_008 : List Nat := [5662,5663,5672,5677,5680,5681,5685,5688,5698,5699,5703,5706,5709,5712,5716,5717,5726,5731,5734,5735,5739,5742,6493,6495,6501,6503,6508,6510,7378,7379,7382,7383]
def ridgeSupport261_009 : List Nat := [7386,7387,7401,7403,7412,7417,7418,7423,7628,7629,7630,7631,7632,7633,7885,7893,7900]
def ridgeSupport261_code : Nat := 0x1edcf6afb37ba3dd0ee7f73bb9bdcce7ff3eb9f3cf4e75f3a79b7cdae6bf35b9a7cd2cb765b32cf965cafe576cdd66bb33d99acc765eb2ad952ca164db25591ec87642b1c58d6c63630b16d8a2c3f61eb0d585ec29611b06d832b955c8ae3d71ab7f5bdadad6d2b595aaad35692b475a2a89d44aa1b50ba855422a09502a80d4029ff4fea7ed3f29f54f7a7a53c69d94eaa74d3a29cf4e6a72d3929c54dfa6e53669a34d0a67d33a99b4cca5cd2e296f4b6a5ad2d294f4a6a51d28a93f49ea4dd26a92f496a49d249d36e977493a41d1ce8c73d39d9ce6e71737b9b5cb4e56729b945c9ee4d4a9a54929c94b4a42515282940497a4b923a91c485a42920c90348023f51f28f8473a3991aa8d443ea1f10e887243721b10d686a42ca16108e8463981cb8e5a72c3959ca8e527283931c8ce4071d38a9c50e267123889c40dfa6fc37d9be8df26f83729b90dc66e23709b80d9a6cc3659b28d926c835a9ad0d666b23589ac0d3a69c34d9a68d326983459a28d0a6843419a08d0268033e99f0cee67633999c8cda66c33599a8cd26683329990cbe65e0cf867833619a0cc065c32a1930c9064031e18d0c5062430c1850c1860830017e0be85ec2f41780b105842b815a0ac855c2ac1550a9054429e14e0a602b41500a7052028c128091047023411407c03c81d80ea07200a0048020003
def ridgeSupport261_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport261_code
def ridgeSupport261_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport261_code
def ridgeSupport261_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport261_code
def ridgeSupport261_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport261_code
def ridgeSupport261_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport261_code
def ridgeSupport261_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport261_code
def ridgeSupport261_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport261_code
def ridgeSupport261_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport261_code
def ridgeSupport261_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport261_code
def ridgeSupport261_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport261_code
def ridgeSupport261_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport261_code
def ridgeSupport261_suffix_010 : List Nat := []
def ridgeSupport261_suffix_009 : List Nat := ridgeSupport261_009 ++ ridgeSupport261_suffix_010
def ridgeSupport261_suffix_008 : List Nat := ridgeSupport261_008 ++ ridgeSupport261_suffix_009
def ridgeSupport261_suffix_007 : List Nat := ridgeSupport261_007 ++ ridgeSupport261_suffix_008
def ridgeSupport261_suffix_006 : List Nat := ridgeSupport261_006 ++ ridgeSupport261_suffix_007
def ridgeSupport261_suffix_005 : List Nat := ridgeSupport261_005 ++ ridgeSupport261_suffix_006
def ridgeSupport261_suffix_004 : List Nat := ridgeSupport261_004 ++ ridgeSupport261_suffix_005
def ridgeSupport261_suffix_003 : List Nat := ridgeSupport261_003 ++ ridgeSupport261_suffix_004
def ridgeSupport261_suffix_002 : List Nat := ridgeSupport261_002 ++ ridgeSupport261_suffix_003
def ridgeSupport261_suffix_001 : List Nat := ridgeSupport261_001 ++ ridgeSupport261_suffix_002
def ridgeSupport261_suffix_000 : List Nat := ridgeSupport261_000 ++ ridgeSupport261_suffix_001
theorem ridgeSupport261_source : candidateSupports 261 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport261_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
