module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public meta import CertificateNumbers
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
cert_ridgeSupport_2 261 7386 7387 7401 7403 7412 7417 7418 7423 7628 7629 7630 7631 7632 7633 7885 7893 7900
cert_ridgeSupport_code_2 261
cert_ridgeSupport_rest 261 000 0
cert_ridgeSupport_rest 261 001 416
cert_ridgeSupport_rest 261 002 832
cert_ridgeSupport_rest 261 003 1248
cert_ridgeSupport_rest 261 004 1664
cert_ridgeSupport_rest 261 005 2080
cert_ridgeSupport_rest 261 006 2496
cert_ridgeSupport_rest 261 007 2912
cert_ridgeSupport_rest 261 008 3328
cert_ridgeSupport_rest 261 009 3744
cert_ridgeSupport_rest 261 010 3965
cert_ridgeSupport_suffix_2 261 010
cert_ridgeSupport_suffix 261 009 010
cert_ridgeSupport_suffix 261 008 009
cert_ridgeSupport_suffix 261 007 008
cert_ridgeSupport_suffix 261 006 007
cert_ridgeSupport_suffix 261 005 006
cert_ridgeSupport_suffix 261 004 005
cert_ridgeSupport_suffix 261 003 004
cert_ridgeSupport_suffix 261 002 003
cert_ridgeSupport_suffix 261 001 002
cert_ridgeSupport_suffix 261 000 001
cert_ridgeSupport_source 261 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
