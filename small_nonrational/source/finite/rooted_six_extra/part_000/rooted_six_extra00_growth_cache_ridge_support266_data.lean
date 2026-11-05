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
def ridgeSupport266_000 : List Nat := [7,47,50,52,54,215,216,218,223,225,239,240,242,247,249,262,265,267,270,272,791,793,796,797,799,815,817,820,821,823,840,842]
def ridgeSupport266_001 : List Nat := [843,846,848,851,852,854,855,858,859,860,862,863,865,870,871,893,895,896,898,899,901,903,904,906,907,910,911,914,916,917,919,920]
def ridgeSupport266_002 : List Nat := [922,924,925,927,928,931,932,3114,3115,3120,3121,3124,3125,3126,3127,3128,3129,3134,3135,3138,3139,3144,3145,3148,3149,3150,3151,3152,3153,3158,3159,3172]
def ridgeSupport266_003 : List Nat := [3173,3174,3175,3176,3177,3196,3197,3198,3199,3200,3201,3220,3221,3222,3223,3224,3225,3244,3245,3246,3247,3248,3249,3268,3269,3270,3271,3272,3273,3292,3293,3294]
def ridgeSupport266_004 : List Nat := [3295,3296,3297,3305,3308,3311,3314,3316,3317,3318,3319,3320,3321,3322,3324,3374,3375,3386,3387,3388,3390,3394,3396,3410,3411,3422,3423,3516,3517,3528,3529,3533]
def ridgeSupport266_005 : List Nat := [3536,3539,3542,3552,3553,3564,3565,3588,3589,3600,3601,3605,3608,3611,3614,3624,3625,3636,3637,5180,5181,5192,5193,5216,5217,5228,5229,5236,5238,5242,5244,5322]
def ridgeSupport266_006 : List Nat := [5323,5334,5335,5358,5359,5370,5371,5381,5384,5387,5390,5394,5395,5406,5407,5430,5431,5442,5443,5453,5456,5459,5462,7228,7229,7230,7231,7232,7233,7948,7949,7950]
def ridgeSupport266_007 : List Nat := [7951,7952,7953,7961,7964,7967,7969,7970,7971,7973,7976,7979,7981,7982,7983,7988,7989,7994,7995,8022,8023,8028,8029,8040,8041,8046,8047,8398,8400,8404,8406,8435]
def ridgeSupport266_008 : List Nat := [8438,8441,8444,8453,8456,8459,8462]
def ridgeSupport266_code : Nat := 0x210e842e10884160fc83e60f683ce0d683520d08339f6f7db9f697da1f5d7d71f577d59f3b7ce9f357cd1f2f7cb9f2d7cadf287c95f237c89f217c7df1c7c65f117c41f0f7c39f0d7c31c417101c3f70f9c3d70f1556554d5505535543550953754d951f5479513544950e542d50854154fb53e94ef53b94d753594cb532947c51e947651d146d51b14615181449512143d50f0e3538d0e2938a0e1e386ce183854e113840e053810ded37b0de13780dd6374cdd03734dc93720dbd36f0d5f3578d533548d443508d3e34f0d3b34e8d2f34b8cfc33e8cf933e0cf733d8cf533d0cf233bccec33a4ce13380cdf3378cdd3370cc93320cc73318cc53310cb132c0caf32b8cad32b0c993260c973258c953250c813200c7f31f8c7d31f0c6931a0c673198c653190c573158c513140c4f3138c4d3130c493120c433108c3f30f8c3930e0c3730d8c3530d0c3130c0c2b30a83a40e8c3a00e7c39d0e7039a0e603970e543940e4838f0e3838b0e283880e1c3850e0c3820e0037f0df43670d983610d7c35e0d7035b0d683570d583540d4c3500d3834b0d283480cdc3350cd03310cbc31f0c7431c0c64317044010e042c10904180f903dc0f203c00ef03840df03680d8035c03600d003200bc007
def ridgeSupport266_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport266_code
def ridgeSupport266_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport266_code
def ridgeSupport266_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport266_code
def ridgeSupport266_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport266_code
def ridgeSupport266_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport266_code
def ridgeSupport266_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport266_code
def ridgeSupport266_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport266_code
def ridgeSupport266_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport266_code
def ridgeSupport266_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport266_code
def ridgeSupport266_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport266_code
def ridgeSupport266_suffix_009 : List Nat := []
def ridgeSupport266_suffix_008 : List Nat := ridgeSupport266_008 ++ ridgeSupport266_suffix_009
def ridgeSupport266_suffix_007 : List Nat := ridgeSupport266_007 ++ ridgeSupport266_suffix_008
def ridgeSupport266_suffix_006 : List Nat := ridgeSupport266_006 ++ ridgeSupport266_suffix_007
def ridgeSupport266_suffix_005 : List Nat := ridgeSupport266_005 ++ ridgeSupport266_suffix_006
def ridgeSupport266_suffix_004 : List Nat := ridgeSupport266_004 ++ ridgeSupport266_suffix_005
def ridgeSupport266_suffix_003 : List Nat := ridgeSupport266_003 ++ ridgeSupport266_suffix_004
def ridgeSupport266_suffix_002 : List Nat := ridgeSupport266_002 ++ ridgeSupport266_suffix_003
def ridgeSupport266_suffix_001 : List Nat := ridgeSupport266_001 ++ ridgeSupport266_suffix_002
def ridgeSupport266_suffix_000 : List Nat := ridgeSupport266_000 ++ ridgeSupport266_suffix_001
theorem ridgeSupport266_source : candidateSupports 266 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport266_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
