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
def ridgeSupport70_000 : List Nat := [1,31,32,33,102,105,107,110,112,114,117,119,122,124,126,129,131,134,136,527,532,533,535,536,537,538,540,541,543,544,546,547]
def ridgeSupport70_001 : List Nat := [553,554,556,557,558,559,561,562,564,565,567,568,574,575,577,578,579,580,582,583,585,586,588,589,1868,1869,1870,1871,1872,1873,1874,1875]
def ridgeSupport70_002 : List Nat := [1880,1881,1886,1887,1892,1893,1894,1895,1896,1897,1898,1899,1904,1905,1910,1911,1916,1917,1918,1919,1920,1921,1940,1941,1942,1943,1944,1945,1964,1965,1966,1967]
def ridgeSupport70_003 : List Nat := [1968,1969,1988,1989,1990,1991,1992,1993,2012,2013,2014,2015,2016,2017,2036,2037,2038,2039,2040,2041,2060,2061,2062,2063,2064,2065,2069,2071,2075,2077,2081,2083]
def ridgeSupport70_004 : List Nat := [2126,2127,2138,2139,2147,2149,2153,2155,2162,2163,2174,2175,2198,2199,2210,2211,2219,2221,2225,2227,2234,2235,2246,2247,2270,2271,2282,2283,2291,2293,2297,2299]
def ridgeSupport70_005 : List Nat := [2306,2307,2318,2319,4748,4750,4752,4754,4759,4763,4764,4766,4768,4770,4775,4779,4780,4782,4784,4786,4791,4795,5396,5397,5398,5399,5400,5401,5408,5409,5410,5411]
def ridgeSupport70_006 : List Nat := [5412,5413,5420,5421,5422,5423,5424,5425,5444,5445,5446,5447,5448,5449,5468,5469,5470,5471,5472,5473,5477,5479,5483,5485,5489,5491,5492,5493,5494,5495,5496,5497]
def ridgeSupport70_007 : List Nat := [5501,5503,5507,5509,5513,5515,5519,5520,5522,5523,5525,5526,5531,5533,5537,5539,5546,5547,5558,5559,5567,5569,5573,5575,5578,5580,5585,5587,5591,5593,5600,5601]
def ridgeSupport70_008 : List Nat := [5612,5613,5621,5623,5627,5629,5632,5634,5639,5641,5645,5647,5654,5655,5666,5667,5675,5677,5681,5683,5686,5688,7124,7126,7128,7130,7132,7134,7388,7389,7390,7391]
def ridgeSupport70_009 : List Nat := [7392,7393,7403,7405,7409,7411,7415,7417,7652,7653,7654,7655,7656,7657,8036,8040,8044]
def ridgeSupport70_code : Nat := 0x1f6cfb47d93bd3de8ef3f79bbcbde4e7cf3df9e7cf1e76f3af9c3ce0e6ff37b9bbcdcdef6f737b5bd8deb6f52c71636b19d8c6c5b62bb11d88ac2f616b07d836c13607b015802bfb5fbafbd7d6bdb5ecaf0d782bb35d7ae9d746b995caae3d716b835bfadbd6dab575aaad1d686b3b59bacb5656b27592ac8563eb17589ac2d60eaff57dabcd5e2aef576abad5d2ae7571ab6d5aeacf565ab0d582abf55eaaed572a93548aa3d51aa8b544a98d4c2a5f52ea96d4b2a4b524a91d48aa43520a8cd462a2f516a8ad4525772b79594ac255d2ac955ca9e5452a094f4a725372979494a4251d28c487a43920690247da3e51ea8f3475a3a91be8de463a3191768ba459a2c515a8ab451a28912e89643fa1f90e6872435a1a50ca86342da16909e84e411a08503a81b40ba055022810407a03901a80c3fc9fe0fee7f63fa9fd0fc27e03ef9f78fba7dc3e49f20f8e7c63e29f10f627b03d79eb8f5a7ac3cc9e60f2e7963ca9e50f027803bf9df8efa77c3bb9dd8ee27703b59da8ed27683b39d98eca7643af9d78eb27583a99d48ea27503a79d38e9a74c12689304942491238918488243121090447e23e11c08dc46a23411908c445e22e11688b0454229111888844021f10e887043421910c085c42a214107822010c08304081f80f807a03b81d40e407003701ac0d2066010808003e001
def ridgeSupport70_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport70_code
def ridgeSupport70_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport70_code
def ridgeSupport70_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport70_code
def ridgeSupport70_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport70_code
def ridgeSupport70_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport70_code
def ridgeSupport70_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport70_code
def ridgeSupport70_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport70_code
def ridgeSupport70_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport70_code
def ridgeSupport70_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport70_code
def ridgeSupport70_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport70_code
def ridgeSupport70_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport70_code
def ridgeSupport70_suffix_010 : List Nat := []
def ridgeSupport70_suffix_009 : List Nat := ridgeSupport70_009 ++ ridgeSupport70_suffix_010
def ridgeSupport70_suffix_008 : List Nat := ridgeSupport70_008 ++ ridgeSupport70_suffix_009
def ridgeSupport70_suffix_007 : List Nat := ridgeSupport70_007 ++ ridgeSupport70_suffix_008
def ridgeSupport70_suffix_006 : List Nat := ridgeSupport70_006 ++ ridgeSupport70_suffix_007
def ridgeSupport70_suffix_005 : List Nat := ridgeSupport70_005 ++ ridgeSupport70_suffix_006
def ridgeSupport70_suffix_004 : List Nat := ridgeSupport70_004 ++ ridgeSupport70_suffix_005
def ridgeSupport70_suffix_003 : List Nat := ridgeSupport70_003 ++ ridgeSupport70_suffix_004
def ridgeSupport70_suffix_002 : List Nat := ridgeSupport70_002 ++ ridgeSupport70_suffix_003
def ridgeSupport70_suffix_001 : List Nat := ridgeSupport70_001 ++ ridgeSupport70_suffix_002
def ridgeSupport70_suffix_000 : List Nat := ridgeSupport70_000 ++ ridgeSupport70_suffix_001
theorem ridgeSupport70_source : candidateSupports 70 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport70_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
