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
def ridgeSupport67_000 : List Nat := [1,5,9,10,11,103,105,106,109,111,115,117,118,121,123,127,129,130,133,135,175,177,178,181,183,187,189,190,193,195,199,201]
def ridgeSupport67_001 : List Nat := [202,205,207,247,248,250,251,252,253,255,256,258,259,261,262,268,269,271,272,273,274,276,277,279,280,282,283,289,290,292,293,294]
def ridgeSupport67_002 : List Nat := [295,297,298,300,301,303,304,1388,1389,1390,1391,1392,1393,1394,1395,1400,1401,1406,1407,1412,1413,1414,1415,1416,1417,1418,1419,1424,1425,1430,1431,1436]
def ridgeSupport67_003 : List Nat := [1437,1438,1439,1440,1441,1460,1461,1462,1463,1464,1465,1484,1485,1486,1487,1488,1489,1508,1509,1510,1511,1512,1513,1532,1533,1534,1535,1536,1537,1556,1557,1558]
def ridgeSupport67_004 : List Nat := [1559,1560,1561,1580,1581,1582,1583,1584,1585,1589,1591,1595,1597,1601,1603,2108,2109,2120,2121,2144,2145,2156,2157,2171,2173,2177,2179,2180,2181,2192,2193,2216]
def ridgeSupport67_005 : List Nat := [2217,2228,2229,2243,2245,2249,2251,2252,2253,2264,2265,2288,2289,2300,2301,2315,2317,2321,2323,2876,2877,2888,2889,2912,2913,2924,2925,2939,2941,2945,2947,2948]
def ridgeSupport67_006 : List Nat := [2949,2960,2961,2984,2985,2996,2997,3011,3013,3017,3019,3020,3021,3032,3033,3056,3057,3068,3069,3083,3085,3089,3091,5132,5133,5134,5135,5136,5137,5168,5169,5174]
def ridgeSupport67_007 : List Nat := [5175,5180,5181,5216,5217,5222,5223,5228,5229,5348,5349,5350,5351,5352,5353,5852,5853,5854,5855,5856,5857,5876,5877,5878,5879,5880,5881,5888,5889,5890,5891,5892]
def ridgeSupport67_008 : List Nat := [5893,6005,6007,6011,6013,6023,6025,6029,6031,6041,6043,6047,6049,6173,6175,6179,6181,6191,6193,6197,6199,6209,6211,6215,6217]
cert_ridgeSupport_code_3 67
cert_ridgeSupport_rest_2 67 000 0
cert_ridgeSupport_rest_2 67 001 416
cert_ridgeSupport_rest_2 67 002 832
cert_ridgeSupport_rest_2 67 003 1248
cert_ridgeSupport_rest_2 67 004 1664
cert_ridgeSupport_rest_2 67 005 2080
cert_ridgeSupport_rest_2 67 006 2496
cert_ridgeSupport_rest_2 67 007 2912
cert_ridgeSupport_rest_2 67 008 3328
cert_ridgeSupport_rest_2 67 009 3653
cert_ridgeSupport_suffix_4 67 009
cert_ridgeSupport_suffix_3 67 008 009
cert_ridgeSupport_suffix_3 67 007 008
cert_ridgeSupport_suffix_3 67 006 007
cert_ridgeSupport_suffix_3 67 005 006
cert_ridgeSupport_suffix_3 67 004 005
cert_ridgeSupport_suffix_3 67 003 004
cert_ridgeSupport_suffix_3 67 002 003
cert_ridgeSupport_suffix_3 67 001 002
cert_ridgeSupport_suffix_3 67 000 001
cert_ridgeSupport_source_3 67 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
