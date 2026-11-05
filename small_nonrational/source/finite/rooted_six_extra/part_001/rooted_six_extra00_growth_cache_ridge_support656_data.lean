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
def ridgeSupport656_000 : List Nat := [59,83,103,119,122,124,671,672,673,674,681,682,827,828,829,830,837,838,957,958,959,962,963,968,969,974,976,998,1000,1002,1004,1006]
def ridgeSupport656_001 : List Nat := [1011,1012,1014,1017,1248,1249,1252,1253,1256,1257,1294,1295,1296,1299,1300,1305,1306,1311,1313,1335,1337,1339,1341,1343,1348,1349,1351,1354,1513,1514,1517,1518]
def ridgeSupport656_002 : List Nat := [1521,1522,1559,1560,1561,1564,1565,1570,1571,1576,1578,1600,1602,1604,1606,1608,1613,1614,1616,1619,1751,1755,1756,1757,1758,1760,1761,1768,1770,1794,1796,1798]
def ridgeSupport656_003 : List Nat := [1799,1801,1803,1804,1808,1813,1814,1816,1818,1820,1821,1823,1825,1826,1830,1832,1837,1838,4168,4173,4182,4184,4250,4251,4260,4261,4266,4267,4270,4272,4276,4277]
def ridgeSupport656_004 : List Nat := [4283,4286,4298,4299,4308,4309,4336,4341,4346,4347,4350,4352,4356,4357,4362,4363,4372,4373,4386,4387,4396,4397,4408,4413,4422,4424,4490,4491,4500,4501,4506,4507]
def ridgeSupport656_005 : List Nat := [4510,4512,4516,4517,4523,4526,4538,4539,4548,4549,4576,4581,4586,4587,4590,4592,4596,4597,4602,4603,4612,4613,4626,4627,4636,4637,4728,4730,4740,4742,4756,4757]
def ridgeSupport656_006 : List Nat := [4768,4769,4870,4875,4882,4887,4902,4903,4914,4915,4936,4941,4950,4952,5018,5019,5028,5029,5034,5035,5038,5040,5044,5045,5051,5054,5066,5067,5076,5077,5104,5109]
def ridgeSupport656_007 : List Nat := [5114,5115,5118,5120,5124,5125,5130,5131,5140,5141,5154,5155,5164,5165,5256,5258,5268,5270,5284,5285,5296,5297,5398,5403,5410,5415,5430,5431,5442,5443,6256,6261]
def ridgeSupport656_008 : List Nat := [6270,6272,6290,6291,6300,6301,6338,6339,6348,6349,6354,6355,6358,6360,6364,6365,6371,6374,6376,6381,6386,6387,6390,6392,6396,6397,6434,6435,6444,6445,6458,6459]
def ridgeSupport656_009 : List Nat := [6468,6469,6546,6548,6576,6578,6586,6587,6604,6605,6688,6693,6718,6723,6732,6733,6750,6751,6834,6836,6864,6866,6874,6875,6892,6893,6976,6981,7006,7011,7020,7021]
def ridgeSupport656_010 : List Nat := [7038,7039,7362,7363,7398,7399,7458,7459,7620,7621,8186,8187,8196,8197,8201,8202,8203,8204,8209,8210,8234,8235,8244,8245,8249,8250,8251,8252,8257,8258,8290,8291]
def ridgeSupport656_011 : List Nat := [8293,8295,8327,8328,8329,8330,8354,8355,8364,8365,8369,8370,8371,8372,8377,8378,8410,8411,8413,8415,8447,8448,8449,8450,8638,8640,8651,8654,8669,8670,8671,8672]
def ridgeSupport656_012 : List Nat := [8677,8678,8704,8705,8707,8709,8741,8742,8743,8744,8776,8777,8779,8781,8813,8814,8815,8816]
def ridgeSupport656_code : Nat := 0x89c226f89ba26d893624b892624888a2227889a22588162038806200879a1e587821df877a1dd873a1cb87021be840a10184020ff837e0dd836e0da82ea0b982d20b382ca0b182b60ac828e0a2822a0898222087819e065818e062810a04180f203b80ea03980d603480ae02a804a011803200b802a00980160047fedffa7715dc4748dd22739dce6730dcc26dfdb7e6db5b6c6d8db5e6d15b406bb5aec6b6dada6b49ad06ad1ab2697da5e6935a4c690da3e6895a2067359cc66ed9ba66c99b06651992651594464ed93a64b592c648d92263f58fc63e18f663cd8f263b58e863998e363758dc63618d6634d8d263358cc630d8c2627589c624d892620187e61d5870550d54254dd536549d522546d51652c54b052954a45259494522948850b542c508d4225055414502d40a501540450013fe4fed3fa4fd53f04f553d44f2d3ca4ef93bb4ed53b44ec13ae4ead3aa4e953a44e6d39a4d613564d353484ccd3324c9d3264c5d3124c2d3064a852a04a552944a1928449e9278487521c484d212481520447ed1fa47d51f447c11ee47ad1ea47951e047151c446ed1ba46b91ab46951a4468119e466d19a4655194462d18a452114644f513844b512c448d1224455114442d10a441510444010fe43ed0fa43d50f043550d4432d0ca42f90bb42d50b442c10ae42ad0aa42950a4426d09a416105641350481cb872d1ca07261c887211c7c71d1c7071a1c607161c547101c3070b1c247071c187041c086ea1ba06e11b806de1b746dc1b6c6d7194c650193864d19206461910642190062a18a0623188861d1870619186061717c85f117b85ed17a85e91528547151454414fc53d14ec53914dc521147c51a1464514144c510143c50e13a44e813944e413844e00fe43f60fd03f30fb83ec0fa83e80f983d00f383c90f203c30f083bf0ef83bd0d183450cf833d0cf033b0aa82a90a882a10a8029f01f007a01dc067014c03b
def ridgeSupport656_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport656_code
def ridgeSupport656_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport656_code
def ridgeSupport656_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport656_code
def ridgeSupport656_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport656_code
def ridgeSupport656_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport656_code
def ridgeSupport656_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport656_code
def ridgeSupport656_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport656_code
def ridgeSupport656_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport656_code
def ridgeSupport656_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport656_code
def ridgeSupport656_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport656_code
def ridgeSupport656_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport656_code
def ridgeSupport656_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport656_code
def ridgeSupport656_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport656_code
def ridgeSupport656_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport656_code
def ridgeSupport656_suffix_013 : List Nat := []
def ridgeSupport656_suffix_012 : List Nat := ridgeSupport656_012 ++ ridgeSupport656_suffix_013
def ridgeSupport656_suffix_011 : List Nat := ridgeSupport656_011 ++ ridgeSupport656_suffix_012
def ridgeSupport656_suffix_010 : List Nat := ridgeSupport656_010 ++ ridgeSupport656_suffix_011
def ridgeSupport656_suffix_009 : List Nat := ridgeSupport656_009 ++ ridgeSupport656_suffix_010
def ridgeSupport656_suffix_008 : List Nat := ridgeSupport656_008 ++ ridgeSupport656_suffix_009
def ridgeSupport656_suffix_007 : List Nat := ridgeSupport656_007 ++ ridgeSupport656_suffix_008
def ridgeSupport656_suffix_006 : List Nat := ridgeSupport656_006 ++ ridgeSupport656_suffix_007
def ridgeSupport656_suffix_005 : List Nat := ridgeSupport656_005 ++ ridgeSupport656_suffix_006
def ridgeSupport656_suffix_004 : List Nat := ridgeSupport656_004 ++ ridgeSupport656_suffix_005
def ridgeSupport656_suffix_003 : List Nat := ridgeSupport656_003 ++ ridgeSupport656_suffix_004
def ridgeSupport656_suffix_002 : List Nat := ridgeSupport656_002 ++ ridgeSupport656_suffix_003
def ridgeSupport656_suffix_001 : List Nat := ridgeSupport656_001 ++ ridgeSupport656_suffix_002
def ridgeSupport656_suffix_000 : List Nat := ridgeSupport656_000 ++ ridgeSupport656_suffix_001
theorem ridgeSupport656_source : candidateSupports 656 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport656_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
