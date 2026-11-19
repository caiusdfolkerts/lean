module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
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
def ridgeSupport69_000 : List Nat := [1,15,16,17,103,104,107,108,113,115,116,119,120,125,127,128,131,132,137,330,335,336,338,339,340,341,343,344,346,347,349,350]
def ridgeSupport69_001 : List Nat := [356,357,359,360,361,362,364,365,367,368,370,371,377,378,380,381,382,383,385,386,388,389,391,392,1628,1629,1630,1631,1632,1633,1634,1635]
def ridgeSupport69_002 : List Nat := [1640,1641,1646,1647,1652,1653,1654,1655,1656,1657,1658,1659,1664,1665,1670,1671,1676,1677,1678,1679,1680,1681,1700,1701,1702,1703,1704,1705,1724,1725,1726,1727]
def ridgeSupport69_003 : List Nat := [1728,1729,1748,1749,1750,1751,1752,1753,1772,1773,1774,1775,1776,1777,1796,1797,1798,1799,1800,1801,1820,1821,1822,1823,1824,1825,1829,1831,1835,1837,1841,1843]
def ridgeSupport69_004 : List Nat := [2114,2115,2132,2133,2150,2151,2159,2161,2165,2167,2168,2169,2186,2187,2204,2205,2222,2223,2231,2233,2237,2239,2240,2241,2258,2259,2276,2277,2294,2295,2303,2305]
def ridgeSupport69_005 : List Nat := [2309,2311,2312,2313,3644,3646,3648,3650,3655,3659,3660,3662,3664,3666,3671,3675,3676,3678,3680,3682,3687,3691,5264,5265,5266,5267,5268,5269,5276,5277,5278,5279]
def ridgeSupport69_006 : List Nat := [5280,5281,5288,5289,5290,5291,5292,5293,5312,5313,5314,5315,5316,5317,5336,5337,5338,5339,5340,5341,5345,5347,5351,5353,5357,5359,5360,5361,5362,5363,5364,5365]
def ridgeSupport69_007 : List Nat := [5369,5371,5375,5377,5381,5383,5387,5388,5390,5391,5393,5394,5534,5535,5543,5545,5549,5551,5552,5553,5566,5568,5570,5571,5579,5581,5588,5589,5597,5599,5603,5605]
def ridgeSupport69_008 : List Nat := [5606,5607,5620,5622,5624,5625,5633,5635,5642,5643,5651,5653,5657,5659,5660,5661,5674,5676,5678,5679,5687,5689,6488,6490,6492,6494,6496,6498,7376,7377,7378,7379]
cert_ridgeSupport_2 69 7380 7381 7402 7404 7408 7410 7414 7416 7616 7617 7618 7619 7620 7621 7880 7884 7888
cert_ridgeSupport_code_2 69
cert_ridgeSupport_rest 69 000 0
cert_ridgeSupport_rest 69 001 416
cert_ridgeSupport_rest 69 002 832
cert_ridgeSupport_rest 69 003 1248
cert_ridgeSupport_rest 69 004 1664
cert_ridgeSupport_rest 69 005 2080
cert_ridgeSupport_rest 69 006 2496
cert_ridgeSupport_rest 69 007 2912
cert_ridgeSupport_rest 69 008 3328
cert_ridgeSupport_rest 69 009 3744
cert_ridgeSupport_rest 69 010 3965
cert_ridgeSupport_suffix_2 69 010
cert_ridgeSupport_suffix 69 009 010
cert_ridgeSupport_suffix 69 008 009
cert_ridgeSupport_suffix 69 007 008
cert_ridgeSupport_suffix 69 006 007
cert_ridgeSupport_suffix 69 005 006
cert_ridgeSupport_suffix 69 004 005
cert_ridgeSupport_suffix 69 003 004
cert_ridgeSupport_suffix 69 002 003
cert_ridgeSupport_suffix 69 001 002
cert_ridgeSupport_suffix 69 000 001
cert_ridgeSupport_source 69 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
