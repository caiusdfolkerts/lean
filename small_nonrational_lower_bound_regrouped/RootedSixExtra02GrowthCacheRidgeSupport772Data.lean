module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport772_000 : List Nat := [20,36,62,65,66,162,163,164,165,172,173,377,378,379,382,383,388,389,394,396,398,399,400,403,404,409,410,415,417,574,575,576]
def ridgeSupport772_001 : List Nat := [579,580,585,586,591,593,595,596,597,600,601,606,607,612,614,922,926,927,928,929,931,932,939,941,943,947,948,949,950,952,953,960]
def ridgeSupport772_002 : List Nat := [962,964,965,969,970,971,972,974,975,983,985,986,988,1630,1632,1636,1638,1716,1717,1722,1723,1724,1725,1730,1731,1736,1738,1742,1744,1764,1765,1770]
def ridgeSupport772_003 : List Nat := [1771,1798,1800,1804,1806,1812,1813,1818,1819,1820,1821,1826,1827,1844,1845,1850,1851,1870,1872,1876,1878,1956,1957,1962,1963,1964,1965,1970,1971,1976,1978,1982]
def ridgeSupport772_004 : List Nat := [1984,2004,2005,2010,2011,2038,2040,2044,2046,2052,2053,2058,2059,2060,2061,2066,2067,2084,2085,2090,2091,2260,2262,2272,2274,2288,2289,2300,2301,2332,2334,2344]
def ridgeSupport772_005 : List Nat := [2346,2360,2361,2372,2373,3190,3192,3196,3198,3228,3229,3234,3235,3276,3277,3282,3283,3284,3285,3290,3291,3296,3298,3302,3304,3310,3312,3316,3318,3324,3325,3330]
def ridgeSupport772_006 : List Nat := [3331,3372,3373,3378,3379,3396,3397,3402,3403,3726,3727,3738,3739,4830,4831,4838,4839,5146,5148,5150,5152,5158,5160,5162,5164,5180,5181,5186,5187,5243,5245,5247]
def ridgeSupport772_007 : List Nat := [5249,5408,5409,5444,5445,5610,5611,5916,5917,5922,5923,5924,5925,5927,5929,5930,5931,5964,5965,5970,5971,5972,5973,5975,5977,5978,5979,6032,6033,6035,6037,6050]
def ridgeSupport772_008 : List Nat := [6051,6053,6055,6248,6250,6254,6256,6272,6273,6275,6277,6278,6279]
cert_ridgeSupport_code_3 772
cert_ridgeSupport_rest_2 772 000 0
cert_ridgeSupport_rest_2 772 001 416
cert_ridgeSupport_rest_2 772 002 832
cert_ridgeSupport_rest_2 772 003 1248
cert_ridgeSupport_rest_2 772 004 1664
cert_ridgeSupport_rest_2 772 005 2080
cert_ridgeSupport_rest_2 772 006 2496
cert_ridgeSupport_rest_2 772 007 2912
cert_ridgeSupport_rest_2 772 008 3328
cert_ridgeSupport_rest_2 772 009 3497
cert_ridgeSupport_suffix_4 772 009
cert_ridgeSupport_suffix_3 772 008 009
cert_ridgeSupport_suffix_3 772 007 008
cert_ridgeSupport_suffix_3 772 006 007
cert_ridgeSupport_suffix_3 772 005 006
cert_ridgeSupport_suffix_3 772 004 005
cert_ridgeSupport_suffix_3 772 003 004
cert_ridgeSupport_suffix_3 772 002 003
cert_ridgeSupport_suffix_3 772 001 002
cert_ridgeSupport_suffix_3 772 000 001
cert_ridgeSupport_source_3 772 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
