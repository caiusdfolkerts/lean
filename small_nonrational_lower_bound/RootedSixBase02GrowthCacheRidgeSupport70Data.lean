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
def ridgeSupport70_000 : List Nat := [1,31,32,33,102,105,107,110,112,114,117,119,122,124,126,129,131,134,136,527,532,533,535,536,537,538,540,541,543,544,546,547]
def ridgeSupport70_001 : List Nat := [553,554,556,557,558,559,561,562,564,565,567,568,574,575,577,578,579,580,582,583,585,586,588,589,1868,1869,1870,1871,1872,1873,1874,1875]
def ridgeSupport70_002 : List Nat := [1880,1881,1886,1887,1892,1893,1894,1895,1896,1897,1898,1899,1904,1905,1910,1911,1916,1917,1918,1919,1920,1921,1940,1941,1942,1943,1944,1945,1964,1965,1966,1967]
def ridgeSupport70_003 : List Nat := [1968,1969,1988,1989,1990,1991,1992,1993,2012,2013,2014,2015,2016,2017,2036,2037,2038,2039,2040,2041,2060,2061,2062,2063,2064,2065,2069,2071,2075,2077,2081,2083]
def ridgeSupport70_004 : List Nat := [2126,2127,2138,2139,2147,2149,2153,2155,2162,2163,2174,2175,2198,2199,2210,2211,2219,2221,2225,2227,2234,2235,2246,2247,2270,2271,2282,2283,2291,2293,2297,2299]
def ridgeSupport70_005 : List Nat := [2306,2307,2318,2319,4748,4750,4752,4754,4759,4763,4764,4766,4768,4770,4775,4779,4780,4782,4784,4786,4791,4795,5396,5397,5398,5399,5400,5401,5408,5409,5410,5411]
def ridgeSupport70_006 : List Nat := [5412,5413,5420,5421,5422,5423,5424,5425,5444,5445,5446,5447,5448,5449,5468,5469,5470,5471,5472,5473,5477,5479,5483,5485,5489,5491,5492,5493,5494,5495,5496,5497]
def ridgeSupport70_007 : List Nat := [5501,5503,5507,5509,5513,5515,5519,5520,5522,5523,5525,5526,5531,5533,5537,5539,5546,5547,5558,5559,5567,5569,5573,5575,5578,5580,5585,5587,5591,5593,5600,5601]
def ridgeSupport70_008 : List Nat := [5612,5613,5621,5623,5627,5629,5632,5634,5639,5641,5645,5647,5654,5655,5666,5667,5675,5677,5681,5683,5686,5688,7124,7126,7128,7130,7132,7134,7388,7389,7390,7391]
cert_ridgeSupport_2 70 7392 7393 7403 7405 7409 7411 7415 7417 7652 7653 7654 7655 7656 7657 8036 8040 8044
cert_ridgeSupport_code_2 70
cert_ridgeSupport_rest 70 000 0
cert_ridgeSupport_rest 70 001 416
cert_ridgeSupport_rest 70 002 832
cert_ridgeSupport_rest 70 003 1248
cert_ridgeSupport_rest 70 004 1664
cert_ridgeSupport_rest 70 005 2080
cert_ridgeSupport_rest 70 006 2496
cert_ridgeSupport_rest 70 007 2912
cert_ridgeSupport_rest 70 008 3328
cert_ridgeSupport_rest 70 009 3744
cert_ridgeSupport_rest 70 010 3965
cert_ridgeSupport_suffix_2 70 010
cert_ridgeSupport_suffix 70 009 010
cert_ridgeSupport_suffix 70 008 009
cert_ridgeSupport_suffix 70 007 008
cert_ridgeSupport_suffix 70 006 007
cert_ridgeSupport_suffix 70 005 006
cert_ridgeSupport_suffix 70 004 005
cert_ridgeSupport_suffix 70 003 004
cert_ridgeSupport_suffix 70 002 003
cert_ridgeSupport_suffix 70 001 002
cert_ridgeSupport_suffix 70 000 001
cert_ridgeSupport_source 70 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
