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
def ridgeSupport208_000 : List Nat := [55,79,99,115,121,122,623,624,625,626,633,634,779,780,781,782,789,790,935,936,940,942,943,947,949,950,952,956,957,961,963,964]
def ridgeSupport208_001 : List Nat := [968,970,971,973,1200,1201,1204,1205,1208,1209,1272,1273,1277,1279,1280,1284,1286,1287,1289,1293,1294,1298,1300,1301,1305,1307,1308,1310,1465,1466,1469,1470]
def ridgeSupport208_002 : List Nat := [1473,1474,1537,1538,1542,1544,1545,1549,1551,1552,1554,1558,1559,1563,1565,1566,1570,1572,1573,1575,1732,1733,1734,1737,1738,1739,1741,1746,1748,1753,1754,1755]
def ridgeSupport208_003 : List Nat := [1758,1759,1760,1762,1767,1769,1816,1817,1819,1820,1821,1822,1824,1825,1827,1828,1830,1831,4181,4183,4187,4189,4240,4241,4246,4247,4267,4269,4273,4275,4280,4281]
def ridgeSupport208_004 : List Nat := [4286,4287,4288,4289,4294,4295,4336,4337,4342,4343,4349,4351,4355,4357,4376,4377,4382,4383,4400,4401,4406,4407,4421,4423,4427,4429,4480,4481,4486,4487,4507,4509]
def ridgeSupport208_005 : List Nat := [4513,4515,4520,4521,4526,4527,4528,4529,4534,4535,4576,4577,4582,4583,4589,4591,4595,4597,4616,4617,4622,4623,4640,4641,4646,4647,4655,4657,4667,4669,4688,4689]
def ridgeSupport208_006 : List Nat := [4700,4701,4727,4729,4739,4741,4760,4761,4772,4773,4949,4951,4955,4957,5008,5009,5014,5015,5035,5037,5041,5043,5048,5049,5054,5055,5056,5057,5062,5063,5104,5105]
def ridgeSupport208_007 : List Nat := [5110,5111,5117,5119,5123,5125,5144,5145,5150,5151,5168,5169,5174,5175,5183,5185,5195,5197,5216,5217,5228,5229,5255,5257,5267,5269,5288,5289,5300,5301,6269,6271]
def ridgeSupport208_008 : List Nat := [6275,6277,6280,6281,6286,6287,6328,6329,6334,6335,6355,6357,6361,6363,6368,6369,6374,6375,6376,6377,6382,6383,6389,6391,6395,6397,6424,6425,6430,6431,6448,6449]
def ridgeSupport208_009 : List Nat := [6454,6455,6473,6475,6503,6505,6518,6519,6536,6537,6545,6547,6575,6577,6590,6591,6608,6609,6761,6763,6791,6793,6806,6807,6824,6825,6833,6835,6863,6865,6878,6879]
def ridgeSupport208_010 : List Nat := [6896,6897,7370,7371,7406,7407,7466,7467,7612,7613,8176,8177,8182,8183,8200,8201,8206,8207,8210,8211,8224,8225,8230,8231,8248,8249,8254,8255,8258,8259,8272,8274]
def ridgeSupport208_011 : List Nat := [8276,8277,8290,8292,8294,8295,8344,8345,8350,8351,8368,8369,8374,8375,8378,8379,8392,8394,8396,8397,8410,8412,8414,8415,8635,8637,8641,8643,8668,8669,8674,8675]
def ridgeSupport208_012 : List Nat := [8678,8679,8686,8688,8690,8691,8704,8706,8708,8709,8758,8760,8762,8763,8776,8778,8780,8781]
def ridgeSupport208_code : Nat := 0x893624c892a24888ee23a88e22368816204880a20087ce1f287c21ee879e1e6878e1e287761dc870e1c186f61bb837e0de83720da83360cc832a0c882ee0ba82de0b682c60b0827e09e8266098819e06681920628156054814a050810e04280fe03e80e6038809e0268086020804e012803e00e80260087fddff67fc5ff076f5dbc74add2a73bdcee732dcca6bc5af06b7dade6b45acf6acdab16aa5aa86a5da966a25a8769ada6967459d066fd9be66c59af664d991662598865dd97665a5967652d94964dd93664c5930647d91e646591863f58fb63dd8f563bd8ee63a58e8639d8e663858e0636d8d963558d362fd8be62e58b8623d88e6225888621588361fd87d52d54b452a54a85255493522548751b546c5185460513544b510543f50dd43650c5430507d41e506541850154034ffd3fd4fdd3f64fc53f04f1d3c64f053c04efd3be4ee53b84ecd3b14eb53ab4e5d3964e453904d7535b4d5d3554a952a44a652984a1528349e5277497525c494525048f523b48c522f489d2264885220483d20e482520847d51f347bd1ed479d1e647851e046dd1b646c51b046bd1ae46a51a8468d1a1467519b461d1864605180453514b451d14544dd13644c5130447d11e4465118441510343fd0fd43dd0f643c50f0431d0c643050c042fd0be42e50b842cd0b142b50ab425d0964245090417505b415d0551c9c7261c907231c847201c7871d1c7071b1c647181ba46e71b886e01b7c6de1b6c6da1b646d41b486cd1b2c6ca1b246c61b146c4189c6251890622187861d186c6171858612184060f18346091820606180860117085c116f85bd16e85b9147851c146c5191454514144850e1434509141c506141050013fc4fd13e44f812e44b812d44b412c44b00f343cb0f283c80f103c30f043bd0ef03b80ed83b50ecc3af0eb83ac0ea03a70c583150c3830d0c3030b09e827909c827109c026f01e807901cc063013c037
def ridgeSupport208_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport208_code
def ridgeSupport208_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport208_code
def ridgeSupport208_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport208_code
def ridgeSupport208_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport208_code
def ridgeSupport208_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport208_code
def ridgeSupport208_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport208_code
def ridgeSupport208_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport208_code
def ridgeSupport208_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport208_code
def ridgeSupport208_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport208_code
def ridgeSupport208_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport208_code
def ridgeSupport208_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport208_code
def ridgeSupport208_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport208_code
def ridgeSupport208_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport208_code
def ridgeSupport208_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport208_code
def ridgeSupport208_suffix_013 : List Nat := []
def ridgeSupport208_suffix_012 : List Nat := ridgeSupport208_012 ++ ridgeSupport208_suffix_013
def ridgeSupport208_suffix_011 : List Nat := ridgeSupport208_011 ++ ridgeSupport208_suffix_012
def ridgeSupport208_suffix_010 : List Nat := ridgeSupport208_010 ++ ridgeSupport208_suffix_011
def ridgeSupport208_suffix_009 : List Nat := ridgeSupport208_009 ++ ridgeSupport208_suffix_010
def ridgeSupport208_suffix_008 : List Nat := ridgeSupport208_008 ++ ridgeSupport208_suffix_009
def ridgeSupport208_suffix_007 : List Nat := ridgeSupport208_007 ++ ridgeSupport208_suffix_008
def ridgeSupport208_suffix_006 : List Nat := ridgeSupport208_006 ++ ridgeSupport208_suffix_007
def ridgeSupport208_suffix_005 : List Nat := ridgeSupport208_005 ++ ridgeSupport208_suffix_006
def ridgeSupport208_suffix_004 : List Nat := ridgeSupport208_004 ++ ridgeSupport208_suffix_005
def ridgeSupport208_suffix_003 : List Nat := ridgeSupport208_003 ++ ridgeSupport208_suffix_004
def ridgeSupport208_suffix_002 : List Nat := ridgeSupport208_002 ++ ridgeSupport208_suffix_003
def ridgeSupport208_suffix_001 : List Nat := ridgeSupport208_001 ++ ridgeSupport208_suffix_002
def ridgeSupport208_suffix_000 : List Nat := ridgeSupport208_000 ++ ridgeSupport208_suffix_001
theorem ridgeSupport208_source : candidateSupports 208 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport208_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
