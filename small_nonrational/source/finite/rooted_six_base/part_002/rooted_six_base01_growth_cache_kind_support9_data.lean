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
def kindSupport9_000 : List Nat := [14682,14683,14684,14685,14686,14687,14688,14689,14690,14691,14692,14693,14694,14695,14696,14697,14698,14699,14700,14701,14702,14703,14704,14705,14706,14707,14708,14709,14710,14711,14712,14713]
def kindSupport9_001 : List Nat := [14714,14715,14716,14717,14718,14719,14720,14721,14722,14723,14724,14725,14726,14727,14728,14729,14730,14731,14732,14733,14734,14735,14736,14737,14738,14739,14740,14741,14742,14743,14744,14745]
def kindSupport9_002 : List Nat := [14746,14747,14748,14749,14750,14751,14752,14753,14754,14755,14756,14757,14758,14759,14760,14761,14762,14763,14764,14765,14766,14767,14768,14769,14770,14771,14772,14773,14774,14775,14776,14777]
def kindSupport9_003 : List Nat := [14778,14779,14780,14781,14782,14783,14784,14785,14786,14787,14788,14789,14790,14791,14792,14793,14794,14795,14796,14797,14798,14799,14800,14801,14802,14803,14804,14805,14806,14807,14808,14809]
def kindSupport9_004 : List Nat := [14810,14811,14812,14813,14814,14815,14816,14817,14818,14819,14820,14821,14822,14823,14824,14825,14826,14827,14828,14829,14830,14831,14832,14833,14834,14835,14836,14837,14838,14839,14840,14841]
def kindSupport9_005 : List Nat := [14842,14843,14844,14845,14846,14847,14848,14849,14850,14851,14852,14853,14854,14855,14856,14857,14858,14859,14860,14861,14862,14863,14864,14865,14866,14867,14868,14869,14870,14871,14872,14873]
def kindSupport9_006 : List Nat := [14874,14875,14876,14877,14878,14879,14880,14881,14882,14883,14884,14885,14886,14887,14888,14889,14890,14891,14892,14893,14894,14895,14896,14897,14898,14899,14900,14901,14902,14903,14904,14905]
def kindSupport9_007 : List Nat := [14906,14907,14908,14909,14910,14911,14912,14913,14914,14915,14916,14917,14918,14919,14920,14921,14922,14923,14924,14925,14926,14927,14928,14929,14930,14931,14932,14933,14934,14935,14936,14937]
def kindSupport9_008 : List Nat := [14938,14939,14940,14941,14942,14943,14944,14945,14946,14947,14948,14949,14950,14951,14952,14953,14954,14955,14956,14957,14958,14959,14960,14961,14962,14963,14964,14965,14966,14967,14968,14969]
def kindSupport9_009 : List Nat := [14970,14971,14972,14973,14974,14975,14976,14977,14978,14979,14980,14981,14982,14983,14984,14985,14986,14987,14988,14989,14990,14991,14992,14993,14994,14995,14996,14997,14998,14999,15000,15001]
def kindSupport9_010 : List Nat := [15002,15003,15004,15005,15006,15007,15008,15009,15010,15011,15012,15013,15014,15015,15016,15017,15018,15019,15020,15021,15022,15023,15024,15025,15026,15027,15028,15029,15030,15031,15032,15033]
def kindSupport9_011 : List Nat := [15034,15035,15036,15037,15038,15039,15040,15041,15042,15043,15044,15045,15046,15047,15048,15049,15050,15051,15052,15053,15054,15055,15056,15057,15058,15059,15060,15061,15062,15063,15064,15065]
def kindSupport9_012 : List Nat := [15066,15067,15068,15069,15070,15071,15072,15073,15074,15075,15076,15077,15078,15079,15080,15081,15082,15083,15084,15085,15086,15087,15088,15089,15090,15091,15092,15093,15094,15095,15096,15097]
def kindSupport9_013 : List Nat := [15098,15099,15100,15101,15102,15103,15104,15105,15106,15107,15108,15109,15110,15111,15112,15113,15114,15115,15116,15117,15118,15119,15120,15121,15122,15123,15124,15125,15126,15127,15128,15129]
def kindSupport9_014 : List Nat := [15130,15131,15132,15133,15134,15135,15136,15137,15138,15139,15140,15141,15142,15143,15144,15145,15146,15147,15148,15149,15150,15151,15152,15153,15154,15155,15156,15157,15158,15159,15160,15161]
def kindSupport9_015 : List Nat := [15162,15163,15164,15165,15166,15167,15168,15169,15170,15171,15172,15173,15174,15175,15176,15177,15178,15179,15180,15181,15182,15183,15184,15185,15186,15187,15188,15189,15190,15191,15192,15193]
def kindSupport9_016 : List Nat := [15194,15195,15196,15197,15198,15199,15200,15201,15202,15203,15204,15205,15206,15207,15208,15209,15210,15211,15212,15213,15214,15215,15216,15217,15218,15219,15220,15221,15222,15223,15224,15225]
def kindSupport9_017 : List Nat := [15226,15227,15228,15229,15230,15231,15232,15233,15234,15235,15236,15237,15238,15239,15240,15241,15242,15243,15244,15245]
def kindSupport9_code : Nat := 0xee37b8cee2fb8aee27b88ee1fb86ee17b84ee0fb82ee07b80edffb7eedf7b7cedefb7aede7b78eddfb76edd7b74edcfb72edc7b70edbfb6eedb7b6cedafb6aeda7b68ed9fb66ed97b64ed8fb62ed87b60ed7fb5eed77b5ced6fb5aed67b58ed5fb56ed57b54ed4fb52ed47b50ed3fb4eed37b4ced2fb4aed27b48ed1fb46ed17b44ed0fb42ed07b40ecffb3eecf7b3cecefb3aece7b38ecdfb36ecd7b34eccfb32ecc7b30ecbfb2eecb7b2cecafb2aeca7b28ec9fb26ec97b24ec8fb22ec87b20ec7fb1eec77b1cec6fb1aec67b18ec5fb16ec57b14ec4fb12ec47b10ec3fb0eec37b0cec2fb0aec27b08ec1fb06ec17b04ec0fb02ec07b00ebffafeebf7afcebefafaebe7af8ebdfaf6ebd7af4ebcfaf2ebc7af0ebbfaeeebb7aecebafaeaeba7ae8eb9fae6eb97ae4eb8fae2eb87ae0eb7fadeeb77adceb6fadaeb67ad8eb5fad6eb57ad4eb4fad2eb47ad0eb3faceeb37acceb2facaeb27ac8eb1fac6eb17ac4eb0fac2eb07ac0eaffabeeaf7abceaefabaeae7ab8eadfab6ead7ab4eacfab2eac7ab0eabfaaeeab7aaceaafaaaeaa7aa8ea9faa6ea97aa4ea8faa2ea87aa0ea7fa9eea77a9cea6fa9aea67a98ea5fa96ea57a94ea4fa92ea47a90ea3fa8eea37a8cea2fa8aea27a88ea1fa86ea17a84ea0fa82ea07a80e9ffa7ee9f7a7ce9efa7ae9e7a78e9dfa76e9d7a74e9cfa72e9c7a70e9bfa6ee9b7a6ce9afa6ae9a7a68e99fa66e997a64e98fa62e987a60e97fa5ee977a5ce96fa5ae967a58e95fa56e957a54e94fa52e947a50e93fa4ee937a4ce92fa4ae927a48e91fa46e917a44e90fa42e907a40e8ffa3ee8f7a3ce8efa3ae8e7a38e8dfa36e8d7a34e8cfa32e8c7a30e8bfa2ee8b7a2ce8afa2ae8a7a28e89fa26e897a24e88fa22e887a20e87fa1ee877a1ce86fa1ae867a18e85fa16e857a14e84fa12e847a10e83fa0ee837a0ce82fa0ae827a08e81fa06e817a04e80fa02e807a00e7ff9fee7f79fce7ef9fae7e79f8e7df9f6e7d79f4e7cf9f2e7c79f0e7bf9eee7b79ece7af9eae7a79e8e79f9e6e7979e4e78f9e2e7879e0e77f9dee7779dce76f9dae7679d8e75f9d6e7579d4e74f9d2e7479d0e73f9cee7379cce72f9cae7279c8e71f9c6e7179c4e70f9c2e7079c0e6ff9bee6f79bce6ef9bae6e79b8e6df9b6e6d79b4e6cf9b2e6c79b0e6bf9aee6b79ace6af9aae6a79a8e69f9a6e6979a4e68f9a2e6879a0e67f99ee67799ce66f99ae667998e65f996e657994e64f992e647990e63f98ee63798ce62f98ae627988e61f986e617984e60f982e607980e5ff97ee5f797ce5ef97ae5e7978e5df976e5d7974e5cf972e5c7970e5bf96ee5b796ce5af96ae5a7968e59f966e597964e58f962e587960e57f95ee57795ce56f95a
def kindSupport9_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport9_code
def kindSupport9_rest_001 : Nat := PackedRawNatGrowth.drop 448 kindSupport9_code
def kindSupport9_rest_002 : Nat := PackedRawNatGrowth.drop 896 kindSupport9_code
def kindSupport9_rest_003 : Nat := PackedRawNatGrowth.drop 1344 kindSupport9_code
def kindSupport9_rest_004 : Nat := PackedRawNatGrowth.drop 1792 kindSupport9_code
def kindSupport9_rest_005 : Nat := PackedRawNatGrowth.drop 2240 kindSupport9_code
def kindSupport9_rest_006 : Nat := PackedRawNatGrowth.drop 2688 kindSupport9_code
def kindSupport9_rest_007 : Nat := PackedRawNatGrowth.drop 3136 kindSupport9_code
def kindSupport9_rest_008 : Nat := PackedRawNatGrowth.drop 3584 kindSupport9_code
def kindSupport9_rest_009 : Nat := PackedRawNatGrowth.drop 4032 kindSupport9_code
def kindSupport9_rest_010 : Nat := PackedRawNatGrowth.drop 4480 kindSupport9_code
def kindSupport9_rest_011 : Nat := PackedRawNatGrowth.drop 4928 kindSupport9_code
def kindSupport9_rest_012 : Nat := PackedRawNatGrowth.drop 5376 kindSupport9_code
def kindSupport9_rest_013 : Nat := PackedRawNatGrowth.drop 5824 kindSupport9_code
def kindSupport9_rest_014 : Nat := PackedRawNatGrowth.drop 6272 kindSupport9_code
def kindSupport9_rest_015 : Nat := PackedRawNatGrowth.drop 6720 kindSupport9_code
def kindSupport9_rest_016 : Nat := PackedRawNatGrowth.drop 7168 kindSupport9_code
def kindSupport9_rest_017 : Nat := PackedRawNatGrowth.drop 7616 kindSupport9_code
def kindSupport9_rest_018 : Nat := PackedRawNatGrowth.drop 7896 kindSupport9_code
def kindSupport9_suffix_018 : List Nat := []
def kindSupport9_suffix_017 : List Nat := kindSupport9_017 ++ kindSupport9_suffix_018
def kindSupport9_suffix_016 : List Nat := kindSupport9_016 ++ kindSupport9_suffix_017
def kindSupport9_suffix_015 : List Nat := kindSupport9_015 ++ kindSupport9_suffix_016
def kindSupport9_suffix_014 : List Nat := kindSupport9_014 ++ kindSupport9_suffix_015
def kindSupport9_suffix_013 : List Nat := kindSupport9_013 ++ kindSupport9_suffix_014
def kindSupport9_suffix_012 : List Nat := kindSupport9_012 ++ kindSupport9_suffix_013
def kindSupport9_suffix_011 : List Nat := kindSupport9_011 ++ kindSupport9_suffix_012
def kindSupport9_suffix_010 : List Nat := kindSupport9_010 ++ kindSupport9_suffix_011
def kindSupport9_suffix_009 : List Nat := kindSupport9_009 ++ kindSupport9_suffix_010
def kindSupport9_suffix_008 : List Nat := kindSupport9_008 ++ kindSupport9_suffix_009
def kindSupport9_suffix_007 : List Nat := kindSupport9_007 ++ kindSupport9_suffix_008
def kindSupport9_suffix_006 : List Nat := kindSupport9_006 ++ kindSupport9_suffix_007
def kindSupport9_suffix_005 : List Nat := kindSupport9_005 ++ kindSupport9_suffix_006
def kindSupport9_suffix_004 : List Nat := kindSupport9_004 ++ kindSupport9_suffix_005
def kindSupport9_suffix_003 : List Nat := kindSupport9_003 ++ kindSupport9_suffix_004
def kindSupport9_suffix_002 : List Nat := kindSupport9_002 ++ kindSupport9_suffix_003
def kindSupport9_suffix_001 : List Nat := kindSupport9_001 ++ kindSupport9_suffix_002
def kindSupport9_suffix_000 : List Nat := kindSupport9_000 ++ kindSupport9_suffix_001
theorem kindSupport9_source : kindRows 9 =
    (PackedRawNatGrowth.readList 14 564 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
