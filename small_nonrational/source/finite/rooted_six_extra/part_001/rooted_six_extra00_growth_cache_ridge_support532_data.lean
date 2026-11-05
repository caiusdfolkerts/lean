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
def ridgeSupport532_000 : List Nat := [38,78,81,83,84,648,649,651,656,658,672,673,675,680,682,684,685,687,692,694,1224,1226,1229,1230,1232,1248,1250,1253,1254,1256,1260,1262]
def ridgeSupport532_001 : List Nat := [1265,1266,1268,1293,1294,1296,1297,1300,1301,1302,1304,1305,1307,1312,1313,1314,1315,1317,1318,1321,1322,1323,1325,1326,1328,1333,1334,1335,1336,1338,1339,1342]
def ridgeSupport532_002 : List Nat := [1343,1344,1346,1347,1349,1354,1355,4412,4413,4418,4419,4424,4425,4426,4427,4428,4429,4430,4431,4436,4437,4442,4443,4448,4449,4450,4451,4452,4453,4454,4455,4474]
def ridgeSupport532_003 : List Nat := [4475,4476,4477,4478,4479,4498,4499,4500,4501,4502,4503,4522,4523,4524,4525,4526,4527,4546,4547,4548,4549,4550,4551,4570,4571,4572,4573,4574,4575,4594,4595,4596]
def ridgeSupport532_004 : List Nat := [4597,4598,4599,4600,4602,4606,4608,4612,4614,4618,4619,4620,4621,4622,4623,4742,4743,4754,4755,4756,4758,4762,4764,4778,4779,4790,4791,4814,4815,4826,4827,4828]
def ridgeSupport532_005 : List Nat := [4830,4834,4836,4850,4851,4862,4863,4886,4887,4898,4899,4900,4902,4906,4908,4922,4923,4934,4935,6548,6549,6560,6561,6584,6585,6596,6597,6604,6606,6610,6612,6620]
def ridgeSupport532_006 : List Nat := [6621,6632,6633,6656,6657,6668,6669,6676,6678,6682,6684,6692,6693,6704,6705,6728,6729,6740,6741,6748,6750,6754,6756,7390,7391,7392,7393,7394,7395,8242,8243,8244]
def ridgeSupport532_007 : List Nat := [8245,8246,8247,8248,8250,8254,8256,8258,8259,8260,8262,8266,8268,8270,8271,8294,8295,8300,8301,8312,8313,8318,8319,8330,8331,8336,8337,8704,8706,8710,8712,8722]
def ridgeSupport532_008 : List Nat := [8724,8728,8730,8740,8742,8746,8748]
def ridgeSupport532_code : Nat := 0x222c88aa226889221a8862214884a208881a2028802091824208b822a07f81fa07981e206d81b2067819a04f813a04c812a0468112043810a04080fa03a80e203780da03580d203380c9ce37389ce17381cdf7379a646989a5e6971a556951a496921a3168c1a256891a1c6869a166851a0d6831a0168019e967a19dd67719d467499ce67319c567119b966e19a1668199566513474d1933b4ce932c4ca93264c913234c893174c592ff4bf92f34bc92e44b892de4b712db4b692cf4b392b74ad92ab4aa929c4a692964a512934a492874a1920f483920d483120b4829206481120047f91fa47e11f747d91f547d11f347c91df47791dd47711db47691c747191c547111c347091af46b91ad46b11ab46a919746591954651193464917f45f917d45f117b45e9167459916545911634589161458115b4569155455114f453914d453114b45291494521143450913d44f054b1528545150c542150053f14f853b14e853814dc53614d453014b852d14ac52a14a452614945231488521148051b146451814585151450511144050e14344f413c84f113b84ec13a04e613944e213804d013384cd13284c80ad82b40abc2ad0ab02aa0aa02a30a842a00a482900a2c2890a20054014c0510138026
def ridgeSupport532_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport532_code
def ridgeSupport532_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport532_code
def ridgeSupport532_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport532_code
def ridgeSupport532_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport532_code
def ridgeSupport532_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport532_code
def ridgeSupport532_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport532_code
def ridgeSupport532_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport532_code
def ridgeSupport532_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport532_code
def ridgeSupport532_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport532_code
def ridgeSupport532_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport532_code
def ridgeSupport532_suffix_009 : List Nat := []
def ridgeSupport532_suffix_008 : List Nat := ridgeSupport532_008 ++ ridgeSupport532_suffix_009
def ridgeSupport532_suffix_007 : List Nat := ridgeSupport532_007 ++ ridgeSupport532_suffix_008
def ridgeSupport532_suffix_006 : List Nat := ridgeSupport532_006 ++ ridgeSupport532_suffix_007
def ridgeSupport532_suffix_005 : List Nat := ridgeSupport532_005 ++ ridgeSupport532_suffix_006
def ridgeSupport532_suffix_004 : List Nat := ridgeSupport532_004 ++ ridgeSupport532_suffix_005
def ridgeSupport532_suffix_003 : List Nat := ridgeSupport532_003 ++ ridgeSupport532_suffix_004
def ridgeSupport532_suffix_002 : List Nat := ridgeSupport532_002 ++ ridgeSupport532_suffix_003
def ridgeSupport532_suffix_001 : List Nat := ridgeSupport532_001 ++ ridgeSupport532_suffix_002
def ridgeSupport532_suffix_000 : List Nat := ridgeSupport532_000 ++ ridgeSupport532_suffix_001
theorem ridgeSupport532_source : candidateSupports 532 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport532_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
