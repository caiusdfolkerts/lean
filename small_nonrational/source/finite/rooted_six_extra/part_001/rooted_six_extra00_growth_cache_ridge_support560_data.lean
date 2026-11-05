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
def ridgeSupport560_000 : List Nat := [78,98,117,119,120,1225,1226,1228,1233,1235,1249,1250,1252,1257,1259,1261,1262,1264,1269,1271,1490,1491,1493,1498,1500,1514,1515,1517,1522,1524,1526,1527]
def ridgeSupport560_001 : List Nat := [1529,1534,1536,1751,1752,1754,1755,1758,1759,1760,1762,1763,1765,1770,1771,1772,1773,1775,1776,1779,1780,1781,1783,1784,1786,1791,1792,1793,1794,1796,1797,1800]
def ridgeSupport560_002 : List Nat := [1801,1802,1804,1805,1807,1812,1813,6236,6237,6242,6243,6248,6249,6250,6251,6252,6253,6254,6255,6260,6261,6266,6267,6272,6273,6274,6275,6276,6277,6278,6279,6298]
def ridgeSupport560_003 : List Nat := [6299,6300,6301,6302,6303,6322,6323,6324,6325,6326,6327,6346,6347,6348,6349,6350,6351,6370,6371,6372,6373,6374,6375,6394,6395,6396,6397,6398,6399,6418,6419,6420]
def ridgeSupport560_004 : List Nat := [6421,6422,6423,6424,6426,6430,6432,6436,6438,6442,6443,6444,6445,6446,6447,6566,6567,6578,6579,6580,6582,6586,6588,6602,6603,6614,6615,6638,6639,6650,6651,6652]
def ridgeSupport560_005 : List Nat := [6654,6658,6660,6674,6675,6686,6687,6710,6711,6722,6723,6724,6726,6730,6732,6746,6747,6758,6759,6854,6855,6866,6867,6868,6870,6874,6876,6890,6891,6902,6903,6926]
def ridgeSupport560_006 : List Nat := [6927,6938,6939,6940,6942,6946,6948,6962,6963,6974,6975,6998,6999,7010,7011,7012,7014,7018,7020,7034,7035,7046,7047,7606,7607,7608,7609,7610,7611,8650,8651,8652]
def ridgeSupport560_007 : List Nat := [8653,8654,8655,8656,8658,8662,8664,8666,8667,8668,8670,8674,8676,8678,8679,8702,8703,8708,8709,8720,8721,8726,8727,8738,8739,8744,8745,8774,8775,8780,8781,8792]
def ridgeSupport560_008 : List Nat := [8793,8798,8799,8810,8811,8816,8817]
def ridgeSupport560_code : Nat := 0x227189c226b89aa25f897a259896224d8932247891a22988a2223888a217885a211884220588121ff87fa1e7879a1e4878a1de87721db876a1d8875a1d287421cf873a1cd87321cb8729dbb76e9db976e1db776d9b876e19b7b6de9b6c6da9b666d91b636d89b576d59b3f6cf9b336cc9b246c89b1e6c71b1b6c69b0f6c39af76bd9aeb6ba9adc6b69ad66b51ad36b49ac76b19a676999a5b6969a4c6929a466911a436909a3768d9a1f6879a136849a0468099fe67f19fb67e99ef67b99d767599cb67299bc66e99b666d19b366c99a7669992f64b992d64b192b64a99266491920647991a64619176459915645191364498ff63f98fd63f18fb63e98e763998e563918e363898cf63398cd63318cb63298b762d98b562d18b362c989f627989d627189b6269887621988562118836209881620187b61e987561d186f61b986d61b186b61a986961a1863618985d61707151c5070f1c3470c1c287091c207051c107021c047001bfc6fa1be06f71bd46f41bcc6f01bbc6ed1bb06eb1ba86e51b8c6e21b806df1b786db1b686d81b5c60017f85f917dc5f617d05f217b45eb17a85dc17685d5174c5d213dc4f513c04ee13b44eb13a44e413884e1134c4d113304ca132407801dc075018804e
def ridgeSupport560_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport560_code
def ridgeSupport560_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport560_code
def ridgeSupport560_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport560_code
def ridgeSupport560_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport560_code
def ridgeSupport560_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport560_code
def ridgeSupport560_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport560_code
def ridgeSupport560_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport560_code
def ridgeSupport560_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport560_code
def ridgeSupport560_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport560_code
def ridgeSupport560_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport560_code
def ridgeSupport560_suffix_009 : List Nat := []
def ridgeSupport560_suffix_008 : List Nat := ridgeSupport560_008 ++ ridgeSupport560_suffix_009
def ridgeSupport560_suffix_007 : List Nat := ridgeSupport560_007 ++ ridgeSupport560_suffix_008
def ridgeSupport560_suffix_006 : List Nat := ridgeSupport560_006 ++ ridgeSupport560_suffix_007
def ridgeSupport560_suffix_005 : List Nat := ridgeSupport560_005 ++ ridgeSupport560_suffix_006
def ridgeSupport560_suffix_004 : List Nat := ridgeSupport560_004 ++ ridgeSupport560_suffix_005
def ridgeSupport560_suffix_003 : List Nat := ridgeSupport560_003 ++ ridgeSupport560_suffix_004
def ridgeSupport560_suffix_002 : List Nat := ridgeSupport560_002 ++ ridgeSupport560_suffix_003
def ridgeSupport560_suffix_001 : List Nat := ridgeSupport560_001 ++ ridgeSupport560_suffix_002
def ridgeSupport560_suffix_000 : List Nat := ridgeSupport560_000 ++ ridgeSupport560_suffix_001
theorem ridgeSupport560_source : candidateSupports 560 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport560_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
