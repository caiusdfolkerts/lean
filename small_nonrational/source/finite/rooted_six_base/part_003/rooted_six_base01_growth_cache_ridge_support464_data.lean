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
def ridgeSupport464_000 : List Nat := [862,863,864,1199,1200,1201,1504,1505,1506,1598,1599,1600,4524,4525,4526,4527,4528,4529,4620,4621,4622,4623,4624,4625,4716,4717,4718,4719,4720,4721,4788,4789]
def ridgeSupport464_001 : List Nat := [4790,4791,4792,4793,4884,4885,4886,4887,4888,4889,4980,4981,4982,4983,4984,4985,5040,5041,5042,5043,5044,5045,5052,5053,5054,5055,5056,5057,6468,6469,6470,6471]
def ridgeSupport464_002 : List Nat := [6472,6473,6516,6517,6518,6519,6520,6521,6660,6661,6662,6663,6664,6665,6690,6691,6692,6693,6694,6695,6720,6721,6722,6723,6724,6725,9478,9479,9484,9485,9490,9491]
def ridgeSupport464_003 : List Nat := [9498,9500,9504,9506,9510,9512,9526,9527,9532,9533,9538,9539,9618,9620,9624,9626,9630,9632,9666,9668,9672,9674,9678,9680,9718,9719,9724,9725,9730,9731,9738,9740]
def ridgeSupport464_004 : List Nat := [9744,9746,9750,9752,9766,9767,9772,9773,9778,9779,9858,9860,9864,9866,9870,9872,9906,9908,9912,9914,9918,9920,9996,9997,9998,9999,10000,10001,10008,10009,10010,10011]
def ridgeSupport464_005 : List Nat := [10012,10013,11010,11012,11016,11018,11022,11024,11038,11039,11044,11045,11050,11051,11086,11087,11092,11093,11098,11099,11178,11180,11184,11186,11190,11192,11220,11221,11222,11223,11224,11225]
def ridgeSupport464_006 : List Nat := [11286,11287,11288,11289,11290,11291,11316,11317,11318,11319,11320,11321,13086,13088,13092,13146,13148,13152,13154,13158,13160,13218,13220,13224,13278,13280,13284,13286,13290,13292,13380,13381]
def ridgeSupport464_007 : List Nat := [13382,13383,13384,13385,14034,14036,14040,14130,14132,14136,14138,14142,14144,14202,14203,14204,14205,14206,14207,14974,14975,14980,14981,14986,14987,15010,15011,15016,15017,15022,15023,15163]
def ridgeSupport464_008 : List Nat := [15165,15169,15171,15175,15177]
def ridgeSupport464_code : Nat := 0x3b49ed1fb43ed07b3decefaafeabbaa9eaa3aa3ea8ba8bea2ba85ea13a7fe9fb77fddfb77dddf377bddeb740dcfb73adce3734dccb6d8db536d2d127448d11f446d117444cfb33eacf9b3e4cf833decea33a4ce8b368cd9b362cd8335ccd6b324cc8331eb0e6c38b0dec36b0d6c34b06ec1ab066c18b05ec16af66bd8af5ebd6af56bd4aee2bb6aecabb0aeb2baaad6eb5aad56b54ad3eb4eacaeb2aac96b24ac7eb1eac42b0eac2ab08ac12b029c7671c9c6e71a9c667189c467109c3e70e9c3670c9b026be9aea6b89ad26b29a4268e9a2a6889a1268298ce63298b662c989e6269862616984a610983260a980e60297f65fc97de5f697425ce972a5c897125c2968259e966a5989652592950e54294f653c94de53694a2526948a520947251a944e512943650c941e5066915a44690da426905a40689da266895a24688da226825a08681da066815a0465e597865dd97665d59746525948651d94665159444f053c04efd3be4ef53bc4ed53b44ecd3b24ec53b04de53784ddd3764dd53744c653184c5d3164c553144ae52b84add2b64ad52b449c527049bd26e49b526c4845210483d20e483520c46c51b046bd1ae46b51ac190063f18f85e217845e012c44b012bc3600d7c35e
def ridgeSupport464_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport464_code
def ridgeSupport464_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport464_code
def ridgeSupport464_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport464_code
def ridgeSupport464_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport464_code
def ridgeSupport464_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport464_code
def ridgeSupport464_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport464_code
def ridgeSupport464_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport464_code
def ridgeSupport464_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport464_code
def ridgeSupport464_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport464_code
def ridgeSupport464_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport464_code
def ridgeSupport464_suffix_009 : List Nat := []
def ridgeSupport464_suffix_008 : List Nat := ridgeSupport464_008 ++ ridgeSupport464_suffix_009
def ridgeSupport464_suffix_007 : List Nat := ridgeSupport464_007 ++ ridgeSupport464_suffix_008
def ridgeSupport464_suffix_006 : List Nat := ridgeSupport464_006 ++ ridgeSupport464_suffix_007
def ridgeSupport464_suffix_005 : List Nat := ridgeSupport464_005 ++ ridgeSupport464_suffix_006
def ridgeSupport464_suffix_004 : List Nat := ridgeSupport464_004 ++ ridgeSupport464_suffix_005
def ridgeSupport464_suffix_003 : List Nat := ridgeSupport464_003 ++ ridgeSupport464_suffix_004
def ridgeSupport464_suffix_002 : List Nat := ridgeSupport464_002 ++ ridgeSupport464_suffix_003
def ridgeSupport464_suffix_001 : List Nat := ridgeSupport464_001 ++ ridgeSupport464_suffix_002
def ridgeSupport464_suffix_000 : List Nat := ridgeSupport464_000 ++ ridgeSupport464_suffix_001
theorem ridgeSupport464_source : candidateRows 464 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport464_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
