module
prelude
public import RootedSixBase00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport864_000 : List Nat := [1407,1408,1409,1672,1673,1674,1781,1782,1783,1855,1856,1857,10438,10439,10440,10441,10442,10443,10534,10535,10536,10537,10538,10539,10630,10631,10632,10633,10634,10635,10702,10703]
def ridgeSupport864_001 : List Nat := [10704,10705,10706,10707,10798,10799,10800,10801,10802,10803,10894,10895,10896,10897,10898,10899,11182,11183,11184,11185,11186,11187,11194,11195,11196,11197,11198,11199,11398,11399,11400,11401]
def ridgeSupport864_002 : List Nat := [11402,11403,11494,11495,11496,11497,11498,11499,11590,11591,11592,11593,11594,11595,11878,11879,11880,11881,11882,11883,11890,11891,11892,11893,11894,11895,12310,12311,12312,12313,12314,12315]
def ridgeSupport864_003 : List Nat := [12322,12323,12324,12325,12326,12327,16120,16121,16134,16135,16140,16141,16147,16149,16157,16160,16163,16166,16168,16169,16182,16183,16188,16189,16267,16269,16277,16280,16283,16286,16315,16317]
def ridgeSupport864_004 : List Nat := [16325,16328,16331,16334,16360,16361,16374,16375,16380,16381,16387,16389,16397,16400,16403,16406,16408,16409,16422,16423,16428,16429,16507,16509,16517,16520,16523,16526,16555,16557,16565,16568]
def ridgeSupport864_005 : List Nat := [16571,16574,16786,16787,16788,16789,16790,16791,16798,16799,16800,16801,16802,16803,16888,16889,16902,16903,16908,16909,16915,16917,16925,16928,16931,16934,16936,16937,16950,16951,16956,16957]
def ridgeSupport864_006 : List Nat := [17035,17037,17045,17048,17051,17054,17083,17085,17093,17096,17099,17102,17314,17315,17316,17317,17318,17319,17326,17327,17328,17329,17330,17331,17602,17603,17604,17605,17606,17607,17614,17615]
def ridgeSupport864_007 : List Nat := [17616,17617,17618,17619,19987,19989,19994,20047,20049,20057,20060,20063,20066,20119,20121,20126,20179,20181,20189,20192,20195,20198,20386,20387,20388,20389,20390,20391,20467,20469,20474,20527]
def ridgeSupport864_008 : List Nat := [20529,20537,20540,20543,20546,20734,20735,20736,20737,20738,20739,20950,20951,20952,20953,20954,20955,21796,21797,21810,21811,21816,21817,21832,21833,21846,21847,21852,21853,21892,21893,21906]
def ridgeSupport864_009 : List Nat := [21907,21912,21913]
def ridgeSupport864_code : Nat := 0x15666acc5593ab255616ac2555daab9555eaab5549aa9154e6a9c5533aa655496a9251dba3b547668ec51d7a3ad440e8815101a20143fe87f5042a07f40f281cd031a05f3fea7facff39f4f3e9a7d2cfa49f473e8a7734ee39dc13b7676aced39d3d3a6674bce629cbf397272cce519c9f386a70ace1389a7134a268c4d0899f133a263c4c6898b1312261c4c287670eca1d8c3b0875f0eba1d3c3a6874b0e921d1c3a2859d0b2e16442c5857b0aee14f429b85310a56146c28b847b08f211bc236845308a211342238441087610ac213841b0832103c20683f307e20d1c1a2834306820cfc19e832f065a0cac1948327064a05f40bb817102d6056c0ab811d022e044408580fb01ee016c02c804f009a00cc018802d004e008400d800b000dffebffc7feeffd9ff4bfe87f9cff2dfe43fc57f7afeedfcf3f9b7f30fe55fc6bf8b7e7afcf1f9bbf367e52fca1f933f237e40fc75f8abf137e1afc31f83bf067df2fbe1813b026604ac091811b0226036c06980cb018602ec05973bae765ceab9d1739ae725cd6b9a9734ae685cceb9996a5ad4a5a92b5216a3ad4659d6b3a9674ace859ceb399645ac8a5912b221643ac86577eaef95deabbc5776aee95d9abb25762aec15d7abae5526aa49548aa90551eaa39519aa325462a8c1517aa2e53a6a7494e8a9d0539ea7394c5a98a5312a6214c3a9865256a4a9494a928524ea499465a8ca5192a321463a8c60e821d0039f86f70dec1bd434506890d1016042c0057f
def ridgeSupport864_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport864_code
def ridgeSupport864_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport864_code
def ridgeSupport864_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport864_code
def ridgeSupport864_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport864_code
def ridgeSupport864_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport864_code
def ridgeSupport864_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport864_code
def ridgeSupport864_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport864_code
def ridgeSupport864_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport864_code
def ridgeSupport864_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport864_code
def ridgeSupport864_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport864_code
def ridgeSupport864_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport864_code
def ridgeSupport864_suffix_010 : List Nat := []
def ridgeSupport864_suffix_009 : List Nat := ridgeSupport864_009 ++ ridgeSupport864_suffix_010
def ridgeSupport864_suffix_008 : List Nat := ridgeSupport864_008 ++ ridgeSupport864_suffix_009
def ridgeSupport864_suffix_007 : List Nat := ridgeSupport864_007 ++ ridgeSupport864_suffix_008
def ridgeSupport864_suffix_006 : List Nat := ridgeSupport864_006 ++ ridgeSupport864_suffix_007
def ridgeSupport864_suffix_005 : List Nat := ridgeSupport864_005 ++ ridgeSupport864_suffix_006
def ridgeSupport864_suffix_004 : List Nat := ridgeSupport864_004 ++ ridgeSupport864_suffix_005
def ridgeSupport864_suffix_003 : List Nat := ridgeSupport864_003 ++ ridgeSupport864_suffix_004
def ridgeSupport864_suffix_002 : List Nat := ridgeSupport864_002 ++ ridgeSupport864_suffix_003
def ridgeSupport864_suffix_001 : List Nat := ridgeSupport864_001 ++ ridgeSupport864_suffix_002
def ridgeSupport864_suffix_000 : List Nat := ridgeSupport864_000 ++ ridgeSupport864_suffix_001
theorem ridgeSupport864_source : candidateRows 864 =
    (PackedRawNatGrowth.readList 15 291 ridgeSupport864_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
