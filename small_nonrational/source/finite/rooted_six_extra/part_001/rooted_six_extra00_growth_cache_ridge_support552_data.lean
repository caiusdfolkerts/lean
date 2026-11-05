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
def ridgeSupport552_000 : List Nat := [68,98,107,109,110,1069,1070,1072,1077,1079,1093,1094,1096,1101,1103,1105,1106,1108,1113,1115,1489,1492,1493,1496,1499,1513,1516,1517,1520,1523,1525,1528]
def ridgeSupport552_001 : List Nat := [1529,1532,1535,1642,1643,1645,1646,1649,1650,1651,1653,1654,1656,1661,1662,1663,1664,1666,1667,1670,1671,1672,1674,1675,1677,1682,1683,1684,1685,1687,1688,1691]
def ridgeSupport552_002 : List Nat := [1692,1693,1695,1696,1698,1703,1704,5708,5709,5714,5715,5720,5721,5722,5723,5724,5725,5726,5727,5732,5733,5738,5739,5744,5745,5746,5747,5748,5749,5750,5751,5770]
def ridgeSupport552_003 : List Nat := [5771,5772,5773,5774,5775,5794,5795,5796,5797,5798,5799,5818,5819,5820,5821,5822,5823,5842,5843,5844,5845,5846,5847,5866,5867,5868,5869,5870,5871,5890,5891,5892]
def ridgeSupport552_004 : List Nat := [5893,5894,5895,5896,5898,5902,5904,5908,5910,5914,5915,5916,5917,5918,5919,6038,6039,6050,6051,6052,6054,6058,6060,6074,6075,6086,6087,6110,6111,6122,6123,6124]
def ridgeSupport552_005 : List Nat := [6126,6130,6132,6146,6147,6158,6159,6182,6183,6194,6195,6196,6198,6202,6204,6218,6219,6230,6231,6842,6843,6860,6861,6878,6879,6880,6882,6886,6888,6896,6897,6914]
def ridgeSupport552_006 : List Nat := [6915,6932,6933,6950,6951,6952,6954,6958,6960,6968,6969,6986,6987,7004,7005,7022,7023,7024,7026,7030,7032,7040,7041,7546,7547,7548,7549,7550,7551,8530,8531,8532]
def ridgeSupport552_007 : List Nat := [8533,8534,8535,8536,8538,8542,8544,8546,8547,8548,8550,8554,8556,8558,8559,8582,8583,8588,8589,8600,8601,8606,8607,8618,8619,8624,8625,8770,8772,8786,8787,8788]
def ridgeSupport552_008 : List Nat := [8790,8804,8805,8806,8808,8822,8823]
def ridgeSupport552_code : Nat := 0x227789da268899a26589922568952253894a244890a1b186c21ab86aa19f867a199866218d8632187861a16f85ba16c85aa1668592163858a160857a15a8562157855a15585521538549d7f75f9d7d75f1d7b75e9b816e01b786dd9b726dc1b6f6db9b5d6d71b4b6d29b396ce1b306cb9b2a6ca1b276c99b156c51b036c09af16bc1ae86b99ae26b81adf6b79acd6b31abb6ae9857615984b612983c60e983660d183360c9827609980f603980360097f45fc97ee5fb17eb5fa97df5f797c75f197bb5ee97ac5ea97a65e917a35e897975e5971f5c7971d5c7171b5c697165c517105c3970a5c217075c197055c117035c096ef5bb96ed5bb16eb5ba96d75b596d55b516d35b496bf5af96bd5af16bb5ae96a75a996a55a916a35a8968f5a3968d5a3168b5a2967759d967559d167359c967159c166b59a9665599165f597965d597165b59696595961653594964d59306a81a9c6a21a8069f1a7469c1a6c6981a5c6951a506931a4868d1a2c68a1a206871a186831a0868019fc67e19f467819d867519cc67219c466e19b466b19a85ff17f05f917e05f517cc5f017b45ec17a45db17605d517505d1116c4591150452114444f1134448111844510dc43510c042e10b406e01b406b0188044
def ridgeSupport552_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport552_code
def ridgeSupport552_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport552_code
def ridgeSupport552_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport552_code
def ridgeSupport552_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport552_code
def ridgeSupport552_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport552_code
def ridgeSupport552_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport552_code
def ridgeSupport552_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport552_code
def ridgeSupport552_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport552_code
def ridgeSupport552_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport552_code
def ridgeSupport552_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport552_code
def ridgeSupport552_suffix_009 : List Nat := []
def ridgeSupport552_suffix_008 : List Nat := ridgeSupport552_008 ++ ridgeSupport552_suffix_009
def ridgeSupport552_suffix_007 : List Nat := ridgeSupport552_007 ++ ridgeSupport552_suffix_008
def ridgeSupport552_suffix_006 : List Nat := ridgeSupport552_006 ++ ridgeSupport552_suffix_007
def ridgeSupport552_suffix_005 : List Nat := ridgeSupport552_005 ++ ridgeSupport552_suffix_006
def ridgeSupport552_suffix_004 : List Nat := ridgeSupport552_004 ++ ridgeSupport552_suffix_005
def ridgeSupport552_suffix_003 : List Nat := ridgeSupport552_003 ++ ridgeSupport552_suffix_004
def ridgeSupport552_suffix_002 : List Nat := ridgeSupport552_002 ++ ridgeSupport552_suffix_003
def ridgeSupport552_suffix_001 : List Nat := ridgeSupport552_001 ++ ridgeSupport552_suffix_002
def ridgeSupport552_suffix_000 : List Nat := ridgeSupport552_000 ++ ridgeSupport552_suffix_001
theorem ridgeSupport552_source : candidateSupports 552 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport552_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
