module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport560_000 : List Nat := [74,103,105,106,768,1143,1144,1146,1151,1153,1167,1168,1170,1175,1177,1179,1180,1182,1187,1189,1513,1514,1516,1517,1520,1521,1522,1524,1525,1527,1532,1533]
def ridgeSupport560_001 : List Nat := [1534,1535,1537,1538,1541,1542,1543,1545,1546,1548,1553,1554,1555,1556,1558,1559,1562,1563,1564,1566,1567,1569,1574,1575,6430,6431,6436,6437,6442,6443,6444,6445]
def ridgeSupport560_002 : List Nat := [6446,6447,6448,6449,6454,6455,6460,6461,6466,6467,6468,6469,6470,6471,6472,6473,6478,6479,6482,6483,6484,6485,6490,6491,6494,6495,6496,6497,6499,6501,6505,6507]
def ridgeSupport560_003 : List Nat := [6511,6513,6516,6517,6518,6519,6520,6521,6523,6525,6529,6531,6535,6537,6540,6541,6542,6543,6544,6545,6564,6565,6566,6567,6568,6569,6574,6575,6580,6581,6586,6587]
def ridgeSupport560_004 : List Nat := [6598,6599,6604,6605,6610,6611,6618,6620,6622,6623,6624,6626,6628,6629,6630,6632,6634,6635,6642,6644,6646,6647,6648,6650,6652,6653,6654,6656,6658,6659,6667,6669]
def ridgeSupport560_005 : List Nat := [6673,6675,6679,6681,6799,6801,6805,6807,6814,6815,6820,6821,6826,6827,6832,6833,6844,6845,6850,6851,6852,6854,6858,6860,6874,6875,6886,6887,6894,6896,6900,6902]
def ridgeSupport560_006 : List Nat := [6907,6909,6913,6915,6922,6923,6928,6929,6934,6935,6940,6941,6952,6953,6958,6959,6960,6962,6966,6968,6982,6983,6994,6995,7002,7004,7008,7010,7015,7017,7021,7023]
def ridgeSupport560_007 : List Nat := [7030,7031,7036,7037,7042,7043,7048,7049,7060,7061,7066,7067,7068,7070,7074,7076,7090,7091,7102,7103,7110,7112,7116,7118,7138,7140,7142,7145,7154,7156,7158,7161]
def ridgeSupport560_008 : List Nat := [7162,7164,7166,7169,11014,11015,11020,11021,11026,11027,11028,11029,11030,11031,11032,11033,11038,11039,11044,11045,11050,11051,11052,11053,11054,11055,11056,11057,11076,11077,11078,11079]
def ridgeSupport560_009 : List Nat := [11080,11081,11100,11101,11102,11103,11104,11105,11124,11125,11126,11127,11128,11129,11148,11149,11150,11151,11152,11153,11172,11173,11174,11175,11176,11177,11196,11197,11198,11199,11200,11201]
def ridgeSupport560_010 : List Nat := [11202,11204,11208,11210,11214,11216,11220,11221,11222,11223,11224,11225,11344,11345,11356,11357,11358,11360,11364,11366,11380,11381,11392,11393,11416,11417,11428,11429,11430,11432,11436,11438]
def ridgeSupport560_011 : List Nat := [11452,11453,11464,11465,11488,11489,11500,11501,11502,11504,11508,11510,11524,11525,11536,11537,11570,11574,11579,11581,11583,11585,11602,11606,11611,11613,11615,11617,11618,11622,11627,11629]
def ridgeSupport560_012 : List Nat := [11631,11633,14038,14039,14042,14043,14044,14045,14050,14051,14054,14055,14056,14057,14076,14077,14078,14079,14080,14081,14100,14101,14102,14103,14104,14105,14106,14108,14112,14114,14118,14120]
def ridgeSupport560_013 : List Nat := [14124,14125,14126,14127,14128,14129,14130,14132,14136,14138,14142,14144,14148,14149,14150,14151,14152,14153,14155,14156,14158,14159,14161,14162,14220,14222,14226,14228,14242,14243,14254,14255]
def ridgeSupport560_014 : List Nat := [14256,14258,14262,14264,14269,14271,14274,14276,14280,14282,14296,14297,14308,14309,14310,14312,14316,14318,14323,14325,14328,14330,14334,14336,14350,14351,14362,14363,14364,14366,14370,14372]
def ridgeSupport560_015 : List Nat := [14377,14379,14390,14392,14398,14400,14402,14404,14650,14651,14654,14655,14656,14657,14664,14666,14670,14672,14676,14678,15180,15181,15182,15183,15184,15185,15230,15238,15242]
def ridgeSupport560_code : Nat := 0x3b8aee1bb7eed47b50ed3fb4eed37b4ce55b954e54394ee52b948e507940e4ff93ee4ef93ae113842e10383ee0e3836e0af829e093822e07b81ce06f81ae03f80ee0037fedfeb7f8dfd77f3dfbb7ecdfa37e6df977e4df677d8df2b7c8df137c2deff7bddee37b6decb7b0debf7aede8f7a2de53792de3b78cdd4b751dd3f74edd3374bdd27748dd1f746dd17744dd0373edceb738dcd3732dcc7730dcbf72edcb772cdca3726dc8b720dc7371adc67718dc5f716dc57714dc07700dbff6fedbf76fcdba76e8db9f6e6db8f6e2db776dcdb6f6dadb5f6d6b5c6d6fb5b6d6bb59ad62b586d5fb576d5bb55ad52b506d3fb4f6d3bb4dad32b446d10b416d04b3dacf4b3c2ceeb3b6cecb386ce0b326cc8b2f6cbcb2bacacb2a2ca6b296ca4b266c98b206c80b1d6c74b19ac64b182c5eb176c5cb146c50af66bd8af5ebd6af56bd4af42bceaf2abc8af12bc2af06bc0aefebbeaef6bbcaea6ba8ae9eba6ae96ba4ae46b90ae3eb8eae36b8cade6b78addeb76add6b74ad86b60ad7eb5ead76b5cad26b48ad1eb46ad16b44acc6b30acbeb2eacb6b2cacaeb2aac96b24ac7eb1eac66b18ac5eb16ac56b14ac4eb12ac36b0cac1eb067005bfe6ff1bfa6fe5bf66fd1bf26fa5be66f91be26f39bcc6f21bc66efdbbe6ecdbb26e91ba26e79b9c6e6db9a6e55b946e25b886e0db826df5b7c6dddb766dbdb6d6da5b676d89b606d71b5a6d4db526d1db466ce1b366cc9b306cbdb2e6ca5b286c75b1c6c5db166c45b106c2db0a6c0db016bf5afb6bd9af46bc1aee6b9dae66b6dada6b31aca6b19ac46b0dac26af5abc6ac5ab06aadaaa6a95aa46a7da9e6a5da956a45a8f6865a17684da116835a0b680da0268019fe67f59fc67e99f867dd9f667d19f267ad9ea67a19e667959e467899e0677d9de67719da674d9d267359cc671d9c666ed9ba66d59b466bd9ae66a59a8669d9a666959a46645990663d98e663598c6625987660d98165f597b65e597865dd97665d597465c596f65ad96965959636585960657d95e656d95a6555954654d952653d94e6525948651d9466515944650d94264f593c64dd93664c593064bd92e64b592c64ad92a6495924647d91e189c626188461f187861c186c61a185c61618506131848611183060a18246071818605180860117fc5fe17f45fc17dc5f517d05f217c45f017b45ec17a85e912944a3127849c126c499125c492124048f120447f11e847811dc30001a8069019c04a
def ridgeSupport560_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport560_code
def ridgeSupport560_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport560_code
def ridgeSupport560_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport560_code
def ridgeSupport560_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport560_code
def ridgeSupport560_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport560_code
def ridgeSupport560_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport560_code
def ridgeSupport560_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport560_code
def ridgeSupport560_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport560_code
def ridgeSupport560_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport560_code
def ridgeSupport560_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport560_code
def ridgeSupport560_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport560_code
def ridgeSupport560_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport560_code
def ridgeSupport560_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport560_code
def ridgeSupport560_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport560_code
def ridgeSupport560_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport560_code
def ridgeSupport560_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport560_code
def ridgeSupport560_rest_016 : Nat := PackedRawNatGrowth.drop 7126 ridgeSupport560_code
def ridgeSupport560_suffix_016 : List Nat := []
def ridgeSupport560_suffix_015 : List Nat := ridgeSupport560_015 ++ ridgeSupport560_suffix_016
def ridgeSupport560_suffix_014 : List Nat := ridgeSupport560_014 ++ ridgeSupport560_suffix_015
def ridgeSupport560_suffix_013 : List Nat := ridgeSupport560_013 ++ ridgeSupport560_suffix_014
def ridgeSupport560_suffix_012 : List Nat := ridgeSupport560_012 ++ ridgeSupport560_suffix_013
def ridgeSupport560_suffix_011 : List Nat := ridgeSupport560_011 ++ ridgeSupport560_suffix_012
def ridgeSupport560_suffix_010 : List Nat := ridgeSupport560_010 ++ ridgeSupport560_suffix_011
def ridgeSupport560_suffix_009 : List Nat := ridgeSupport560_009 ++ ridgeSupport560_suffix_010
def ridgeSupport560_suffix_008 : List Nat := ridgeSupport560_008 ++ ridgeSupport560_suffix_009
def ridgeSupport560_suffix_007 : List Nat := ridgeSupport560_007 ++ ridgeSupport560_suffix_008
def ridgeSupport560_suffix_006 : List Nat := ridgeSupport560_006 ++ ridgeSupport560_suffix_007
def ridgeSupport560_suffix_005 : List Nat := ridgeSupport560_005 ++ ridgeSupport560_suffix_006
def ridgeSupport560_suffix_004 : List Nat := ridgeSupport560_004 ++ ridgeSupport560_suffix_005
def ridgeSupport560_suffix_003 : List Nat := ridgeSupport560_003 ++ ridgeSupport560_suffix_004
def ridgeSupport560_suffix_002 : List Nat := ridgeSupport560_002 ++ ridgeSupport560_suffix_003
def ridgeSupport560_suffix_001 : List Nat := ridgeSupport560_001 ++ ridgeSupport560_suffix_002
def ridgeSupport560_suffix_000 : List Nat := ridgeSupport560_000 ++ ridgeSupport560_suffix_001
theorem ridgeSupport560_source : candidateRows 560 =
    (PackedRawNatGrowth.readList 14 509 ridgeSupport560_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
