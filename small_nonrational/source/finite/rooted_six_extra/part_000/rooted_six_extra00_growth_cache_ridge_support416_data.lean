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
def ridgeSupport416_000 : List Nat := [88,108,118,125,128,1080,1081,1082,1083,1090,1091,1236,1237,1238,1239,1246,1247,1357,1358,1359,1362,1363,1368,1369,1374,1376,1419,1420,1424,1426,1427,1431]
def ridgeSupport416_001 : List Nat := [1433,1434,1436,1501,1502,1503,1504,1511,1512,1622,1623,1624,1627,1628,1633,1634,1639,1641,1684,1685,1689,1691,1692,1696,1698,1699,1701,1731,1732,1733,1736,1737]
def ridgeSupport416_002 : List Nat := [1742,1743,1748,1750,1793,1794,1798,1800,1801,1805,1807,1808,1810,1839,1842,1843,1844,1847,1848,1849,1851,1856,1857,1859,1860,5465,5467,5484,5486,5544,5545,5550]
def ridgeSupport416_003 : List Nat := [5551,5564,5565,5567,5570,5573,5576,5578,5579,5592,5593,5598,5599,5633,5635,5640,5641,5646,5647,5652,5654,5660,5661,5674,5675,5684,5685,5698,5699,5705,5707,5724]
def ridgeSupport416_004 : List Nat := [5726,5784,5785,5790,5791,5804,5805,5807,5810,5813,5816,5818,5819,5832,5833,5838,5839,5873,5875,5880,5881,5886,5887,5892,5894,5900,5901,5914,5915,5924,5925,5938]
def ridgeSupport416_005 : List Nat := [5939,5952,5954,5964,5966,5980,5981,5992,5993,6167,6169,6179,6181,6200,6201,6212,6213,6233,6235,6252,6254,6312,6313,6318,6319,6332,6333,6335,6338,6341,6344,6346]
def ridgeSupport416_006 : List Nat := [6347,6360,6361,6366,6367,6401,6403,6408,6409,6414,6415,6420,6422,6428,6429,6442,6443,6452,6453,6466,6467,6480,6482,6492,6494,6508,6509,6520,6521,6695,6697,6707]
def ridgeSupport416_007 : List Nat := [6709,6728,6729,6740,6741,6768,6770,6780,6782,6796,6797,6808,6809,6983,6985,6995,6997,7016,7017,7028,7029,7520,7521,7556,7557,7616,7617,8472,8473,8478,8479,8488]
def ridgeSupport416_008 : List Nat := [8490,8492,8493,8496,8499,8520,8521,8526,8527,8536,8538,8540,8541,8544,8547,8560,8561,8563,8565,8614,8616,8618,8619,8640,8641,8646,8647,8656,8658,8660,8661,8664]
def ridgeSupport416_009 : List Nat := [8667,8680,8681,8683,8685,8734,8736,8738,8739,8752,8753,8755,8757,8806,8808,8810,8811]
def ridgeSupport416_code : Nat := 0x226b89aa268899a23588ce23188c2223888a220887a1ed87ae1e987a21db87621d587521d287421c7871a1c187021ab86aa1a8869a17585ce17185c2163858215d857215a856214f853a149852213384c212d84b212a84a211f847a1198461dc17701d857611d617581b756dd1b696da1b556d4db496d1da996a61a8d6a31a7e69f1a7269c1a556951a496921a3568cda29689d97965e196d65b195e65719526541943650993564d192b64a991d6471916645190f6439909642190364058df63798d963618cb63298c863158c262fd8bd62f18af62b98a962a186e61b185b6165845611183960e1825608d819605d7695da175d5d7174e5d317425d017335cc97255c9171b5c6970d5c317065c116ff5bf96f95be16f35bc56cf5b396c95b216bb5ae96b85ad56b25abd6ad5ab169f5a796995a6165e597164b5925643590963558d162b58a961d5871616585160f5839609582160358055df57795d957615cb57295c857155c256fd5bd56f15af56b95a956a156e55b155b55647441d0c7411d0073b1ce47381cdc7341ccc7321cbc7121c4070f1c347091c207061c087011b586d41b3c6ce1b246c81b146c41b0c6a51a8c6a21a8069c1a6c6991a5469419a46671988661197065b196065719585e8179c5e0177c5de177459c1668599165c5931648590163058b158055e1564558154c552153c54e15344df13784d713584d51350443110843b10e843910e008001f407601b0058
def ridgeSupport416_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport416_code
def ridgeSupport416_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport416_code
def ridgeSupport416_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport416_code
def ridgeSupport416_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport416_code
def ridgeSupport416_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport416_code
def ridgeSupport416_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport416_code
def ridgeSupport416_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport416_code
def ridgeSupport416_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport416_code
def ridgeSupport416_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport416_code
def ridgeSupport416_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport416_code
def ridgeSupport416_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport416_code
def ridgeSupport416_suffix_010 : List Nat := []
def ridgeSupport416_suffix_009 : List Nat := ridgeSupport416_009 ++ ridgeSupport416_suffix_010
def ridgeSupport416_suffix_008 : List Nat := ridgeSupport416_008 ++ ridgeSupport416_suffix_009
def ridgeSupport416_suffix_007 : List Nat := ridgeSupport416_007 ++ ridgeSupport416_suffix_008
def ridgeSupport416_suffix_006 : List Nat := ridgeSupport416_006 ++ ridgeSupport416_suffix_007
def ridgeSupport416_suffix_005 : List Nat := ridgeSupport416_005 ++ ridgeSupport416_suffix_006
def ridgeSupport416_suffix_004 : List Nat := ridgeSupport416_004 ++ ridgeSupport416_suffix_005
def ridgeSupport416_suffix_003 : List Nat := ridgeSupport416_003 ++ ridgeSupport416_suffix_004
def ridgeSupport416_suffix_002 : List Nat := ridgeSupport416_002 ++ ridgeSupport416_suffix_003
def ridgeSupport416_suffix_001 : List Nat := ridgeSupport416_001 ++ ridgeSupport416_suffix_002
def ridgeSupport416_suffix_000 : List Nat := ridgeSupport416_000 ++ ridgeSupport416_suffix_001
theorem ridgeSupport416_source : candidateSupports 416 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport416_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
