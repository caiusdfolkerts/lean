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
def ridgeSupport104_000 : List Nat := [65,95,105,106,107,1044,1047,1049,1052,1054,1056,1059,1061,1064,1066,1068,1071,1073,1076,1078,1466,1467,1470,1471,1476,1478,1479,1482,1483,1488,1490,1491]
def ridgeSupport104_001 : List Nat := [1494,1495,1500,1622,1623,1625,1626,1627,1628,1630,1631,1633,1634,1636,1637,1643,1644,1646,1647,1648,1649,1651,1652,1654,1655,1657,1658,1664,1665,1667,1668,1669]
def ridgeSupport104_002 : List Nat := [1670,1672,1673,1675,1676,1678,1679,5704,5705,5706,5707,5708,5709,5710,5711,5716,5717,5722,5723,5728,5729,5730,5731,5732,5733,5734,5735,5740,5741,5746,5747,5752]
def ridgeSupport104_003 : List Nat := [5753,5754,5755,5756,5757,5776,5777,5778,5779,5780,5781,5800,5801,5802,5803,5804,5805,5824,5825,5826,5827,5828,5829,5848,5849,5850,5851,5852,5853,5872,5873,5874]
def ridgeSupport104_004 : List Nat := [5875,5876,5877,5896,5897,5898,5899,5900,5901,5905,5907,5911,5913,5917,5919,5962,5963,5974,5975,5983,5985,5989,5991,5998,5999,6010,6011,6034,6035,6046,6047,6055]
def ridgeSupport104_005 : List Nat := [6057,6061,6063,6070,6071,6082,6083,6106,6107,6118,6119,6127,6129,6133,6135,6142,6143,6154,6155,6766,6767,6784,6785,6802,6803,6811,6813,6817,6819,6820,6821,6838]
def ridgeSupport104_006 : List Nat := [6839,6856,6857,6874,6875,6883,6885,6889,6891,6892,6893,6910,6911,6928,6929,6946,6947,6955,6957,6961,6963,6964,6965,7528,7529,7530,7531,7532,7533,8512,8513,8514]
def ridgeSupport104_007 : List Nat := [8515,8516,8517,8536,8537,8538,8539,8540,8541,8548,8549,8550,8551,8552,8553,8560,8561,8566,8567,8578,8579,8584,8585,8596,8597,8602,8603,8755,8757,8764,8765,8773]
def ridgeSupport104_008 : List Nat := [8775,8782,8783,8791,8793,8800,8801]
def ridgeSupport104_code : Nat := 0x22618982259895e24f893a247891623d88f223588ce19b866a19586521898622183860a17785da17185c216985a2167859a165859215d857215b856a15985621458512143850a1418501d6d75b1d6b75a9d6975a1b356cd1b336cc5b2d6cadb236c89b116c41aff6bf9aed6bb1aeb6ba5ae56b8dadb6b69ac96b21ab76ad9aa56a91aa36a85a9d6a6da936a49a816a01a6f69b980b60297ff5ff97f75fd57f15fbd7e75f997db5f697c35f097b75ed97af5eb57a95e9d79f5e797935e4977b5de976f5db97675d957615d7d7575d5974b5d2971f5c757195c5d7135c4570d5c3170b5c297095c216f55bd16f35bc96f15bc16dd5b716db5b696d95b616c55b116c35b096c15b016ad5ab16ab5aa96a95aa16955a516935a496915a4167d59f167b59e967959e167359c966d59b1667599966559916635989661598165b5969655595164f593964d593164b5929649592068f1a3868c1a2c6891a206861a146841a0c6811a0067a19e467719d867419cc67119c066f19b866c19ac6651990662198465f197865c196c65a196465719585dc175c5d6174c5d217405cb17285c717185c416fc5be16ec5ba10d843410c442f10b042a10a0425108c420107841c1064417105006b01a8069017c041
def ridgeSupport104_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport104_code
def ridgeSupport104_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport104_code
def ridgeSupport104_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport104_code
def ridgeSupport104_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport104_code
def ridgeSupport104_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport104_code
def ridgeSupport104_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport104_code
def ridgeSupport104_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport104_code
def ridgeSupport104_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport104_code
def ridgeSupport104_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport104_code
def ridgeSupport104_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport104_code
def ridgeSupport104_suffix_009 : List Nat := []
def ridgeSupport104_suffix_008 : List Nat := ridgeSupport104_008 ++ ridgeSupport104_suffix_009
def ridgeSupport104_suffix_007 : List Nat := ridgeSupport104_007 ++ ridgeSupport104_suffix_008
def ridgeSupport104_suffix_006 : List Nat := ridgeSupport104_006 ++ ridgeSupport104_suffix_007
def ridgeSupport104_suffix_005 : List Nat := ridgeSupport104_005 ++ ridgeSupport104_suffix_006
def ridgeSupport104_suffix_004 : List Nat := ridgeSupport104_004 ++ ridgeSupport104_suffix_005
def ridgeSupport104_suffix_003 : List Nat := ridgeSupport104_003 ++ ridgeSupport104_suffix_004
def ridgeSupport104_suffix_002 : List Nat := ridgeSupport104_002 ++ ridgeSupport104_suffix_003
def ridgeSupport104_suffix_001 : List Nat := ridgeSupport104_001 ++ ridgeSupport104_suffix_002
def ridgeSupport104_suffix_000 : List Nat := ridgeSupport104_000 ++ ridgeSupport104_suffix_001
theorem ridgeSupport104_source : candidateSupports 104 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport104_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
