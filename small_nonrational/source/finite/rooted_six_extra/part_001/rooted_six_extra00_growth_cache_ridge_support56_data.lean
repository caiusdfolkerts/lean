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
def ridgeSupport56_000 : List Nat := [0,95,96,97,98,1465,1466,1467,1468,1469,1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491]
def ridgeSupport56_001 : List Nat := [1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523]
def ridgeSupport56_002 : List Nat := [1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,6760,6761,6762,6763,6764,6765,6766,6767,6768,6769,6770,6771,6772,6773,6774,6775,6776,6777,6778]
def ridgeSupport56_003 : List Nat := [6779,6780,6781,6782,6783,6784,6785,6786,6787,6788,6789,6790,6791,6792,6793,6794,6795,6796,6797,6798,6799,6800,6801,6802,6803,6804,6805,6806,6807,6808,6809,6810]
def ridgeSupport56_004 : List Nat := [6811,6812,6813,6814,6815,6816,6817,6818,6819,6820,6821,6822,6823,6824,6825,6826,6827,6828,6829,6830,6831,6832,6833,6834,6835,6836,6837,6838,6839,6840,6841,6842]
def ridgeSupport56_005 : List Nat := [6843,6844,6845,6846,6847,6848,6849,6850,6851,6852,6853,6854,6855,6856,6857,6858,6859,6860,6861,6862,6863,6864,6865,6866,6867,6868,6869,6870,6871,6872,6873,6874]
def ridgeSupport56_006 : List Nat := [6875,6876,6877,6878,6879,6880,6881,6882,6883,6884,6885,6886,6887,6888,6889,6890,6891,6892,6893,6894,6895,6896,6897,6898,6899,6900,6901,6902,6903,6904,6905,6906]
def ridgeSupport56_007 : List Nat := [6907,6908,6909,6910,6911,6912,6913,6914,6915,6916,6917,6918,6919,6920,6921,6922,6923,6924,6925,6926,6927,6928,6929,6930,6931,6932,6933,6934,6935,6936,6937,6938]
def ridgeSupport56_008 : List Nat := [6939,6940,6941,6942,6943,6944,6945,6946,6947,6948,6949,6950,6951,6952,6953,6954,6955,6956,6957,6958,6959,6960,6961,6962,6963,6964,6965,6966,6967,6968,6969,6970]
def ridgeSupport56_009 : List Nat := [6971,6972,6973,6974,6975,6976,6977,6978,6979,6980,6981,6982,6983,6984,6985,6986,6987,6988,6989,6990,6991,6992,6993,6994,6995,6996,6997,6998,6999,7000,7001,7002]
def ridgeSupport56_010 : List Nat := [7003,7004,7005,7006,7007,7008,7009,7010,7011,7012,7013,7014,7015,7016,7017,7018,7019,7020,7021,7022,7023,7024,7025,7026,7027,7028,7029,7030,7031,7032,7033,7034]
def ridgeSupport56_011 : List Nat := [7035,7036,7037,7038,7039,7040,7041,7042,7043,7044,7045,7046,7047,7648,7649,7650,7651,7652,7653,7654,7655,7656,7657,7658,7659,7660,7661,7662,7663,7664,7665,7666]
def ridgeSupport56_012 : List Nat := [7667,7668,7669,7670,7671,8752,8753,8754,8755,8756,8757,8758,8759,8760,8761,8762,8763,8764,8765,8766,8767,8768,8769,8770,8771,8772,8773,8774,8775,8776,8777,8778]
def ridgeSupport56_013 : List Nat := [8779,8780,8781,8782,8783,8784,8785,8786,8787,8788,8789,8790,8791,8792,8793,8794,8795,8796,8797,8798,8799,8800,8801,8802,8803,8804,8805,8806,8807,8808,8809,8810]
def ridgeSupport56_014 : List Nat := [8811,8812,8813,8814,8815,8816,8817,8818,8819,8820,8821,8822,8823]
def ridgeSupport56_code : Nat := 0x227789da27589d227389ca27189c226f89ba26d89b226b89aa26989a2267899a2658992263898a261898225f897a25d897225b896a2598962257895a2558952253894a251894224f893a24d893224b892a2498922247891a2458912243890a241890223f88fa23d88f223b88ea23988e223788da23588d223388ca23188c1df777d9df577d1df377c9df177c1def77b9ded77b1deb77a9de977a1de77799de57791de37789de17781b876e19b856e11b836e09b816e01b7f6df9b7d6df1b7b6de9b796de1b776dd9b756dd1b736dc9b716dc1b6f6db9b6d6db1b6b6da9b696da1b676d99b656d91b636d89b616d81b5f6d79b5d6d71b5b6d69b596d61b576d59b556d51b536d49b516d41b4f6d39b4d6d31b4b6d29b496d21b476d19b456d11b436d09b416d01b3f6cf9b3d6cf1b3b6ce9b396ce1b376cd9b356cd1b336cc9b316cc1b2f6cb9b2d6cb1b2b6ca9b296ca1b276c99b256c91b236c89b216c81b1f6c79b1d6c71b1b6c69b196c61b176c59b156c51b136c49b116c41b0f6c39b0d6c31b0b6c29b096c21b076c19b056c11b036c09b016c01aff6bf9afd6bf1afb6be9af96be1af76bd9af56bd1af36bc9af16bc1aef6bb9aed6bb1aeb6ba9ae96ba1ae76b99ae56b91ae36b89ae16b81adf6b79add6b71adb6b69ad96b61ad76b59ad56b51ad36b49ad16b41acf6b39acd6b31acb6b29ac96b21ac76b19ac56b11ac36b09ac16b01abf6af9abd6af1abb6ae9ab96ae1ab76ad9ab56ad1ab36ac9ab16ac1aaf6ab9aad6ab1aab6aa9aa96aa1aa76a99aa56a91aa36a89aa16a81a9f6a79a9d6a71a9b6a69a996a61a976a59a956a51a936a49a916a41a8f6a39a8d6a31a8b6a29a896a21a876a19a856a11a836a09a816a01a7f69f9a7d69f1a7b69e9a7969e1a7769d9a7569d1a7369c9a7169c1a6f69b9a6d69b1a6b69a9a6969a060017fc5fe17f45fc17ec5fa17e45f817dc5f617d45f417cc5f217c45f017bc5ee17b45ec17ac5ea17a45e8179c5e617945e4178c5e217845e0177c5de17745dc176c5da17645d8175c5d617545d4174c5d217445d0173c5ce17345cc172c5ca17245c8171c5c617145c4170c5c217045c016fc5be16f45bc16ec5ba16e40620184060017c000
def ridgeSupport56_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport56_code
def ridgeSupport56_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport56_code
def ridgeSupport56_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport56_code
def ridgeSupport56_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport56_code
def ridgeSupport56_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport56_code
def ridgeSupport56_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport56_code
def ridgeSupport56_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport56_code
def ridgeSupport56_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport56_code
def ridgeSupport56_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport56_code
def ridgeSupport56_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport56_code
def ridgeSupport56_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport56_code
def ridgeSupport56_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport56_code
def ridgeSupport56_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport56_code
def ridgeSupport56_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport56_code
def ridgeSupport56_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport56_code
def ridgeSupport56_rest_015 : Nat := PackedRawNatGrowth.drop 6454 ridgeSupport56_code
def ridgeSupport56_suffix_015 : List Nat := []
def ridgeSupport56_suffix_014 : List Nat := ridgeSupport56_014 ++ ridgeSupport56_suffix_015
def ridgeSupport56_suffix_013 : List Nat := ridgeSupport56_013 ++ ridgeSupport56_suffix_014
def ridgeSupport56_suffix_012 : List Nat := ridgeSupport56_012 ++ ridgeSupport56_suffix_013
def ridgeSupport56_suffix_011 : List Nat := ridgeSupport56_011 ++ ridgeSupport56_suffix_012
def ridgeSupport56_suffix_010 : List Nat := ridgeSupport56_010 ++ ridgeSupport56_suffix_011
def ridgeSupport56_suffix_009 : List Nat := ridgeSupport56_009 ++ ridgeSupport56_suffix_010
def ridgeSupport56_suffix_008 : List Nat := ridgeSupport56_008 ++ ridgeSupport56_suffix_009
def ridgeSupport56_suffix_007 : List Nat := ridgeSupport56_007 ++ ridgeSupport56_suffix_008
def ridgeSupport56_suffix_006 : List Nat := ridgeSupport56_006 ++ ridgeSupport56_suffix_007
def ridgeSupport56_suffix_005 : List Nat := ridgeSupport56_005 ++ ridgeSupport56_suffix_006
def ridgeSupport56_suffix_004 : List Nat := ridgeSupport56_004 ++ ridgeSupport56_suffix_005
def ridgeSupport56_suffix_003 : List Nat := ridgeSupport56_003 ++ ridgeSupport56_suffix_004
def ridgeSupport56_suffix_002 : List Nat := ridgeSupport56_002 ++ ridgeSupport56_suffix_003
def ridgeSupport56_suffix_001 : List Nat := ridgeSupport56_001 ++ ridgeSupport56_suffix_002
def ridgeSupport56_suffix_000 : List Nat := ridgeSupport56_000 ++ ridgeSupport56_suffix_001
theorem ridgeSupport56_source : candidateSupports 56 =
    (PackedRawNatGrowth.readList 14 461 ridgeSupport56_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
