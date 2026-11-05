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
def ridgeSupport928_000 : List Nat := [1428,1429,1430,1693,1694,1695,1802,1803,1804,1852,1853,1854,10432,10433,10434,10435,10436,10437,10528,10529,10530,10531,10532,10533,10624,10625,10626,10627,10628,10629,10696,10697]
def ridgeSupport928_001 : List Nat := [10698,10699,10700,10701,10792,10793,10794,10795,10796,10797,10888,10889,10890,10891,10892,10893,11290,11291,11292,11293,11294,11295,11302,11303,11304,11305,11306,11307,11392,11393,11394,11395]
def ridgeSupport928_002 : List Nat := [11396,11397,11488,11489,11490,11491,11492,11493,11584,11585,11586,11587,11588,11589,11986,11987,11988,11989,11990,11991,11998,11999,12000,12001,12002,12003,12418,12419,12420,12421,12422,12423]
def ridgeSupport928_003 : List Nat := [12430,12431,12432,12433,12434,12435,16126,16127,16132,16133,16138,16139,16153,16155,16159,16161,16165,16167,16174,16175,16180,16181,16186,16187,16273,16275,16279,16281,16285,16287,16321,16323]
def ridgeSupport928_004 : List Nat := [16327,16329,16333,16335,16366,16367,16372,16373,16378,16379,16393,16395,16399,16401,16405,16407,16414,16415,16420,16421,16426,16427,16513,16515,16519,16521,16525,16527,16561,16563,16567,16569]
def ridgeSupport928_005 : List Nat := [16573,16575,16858,16859,16860,16861,16862,16863,16870,16871,16872,16873,16874,16875,16894,16895,16900,16901,16906,16907,16921,16923,16927,16929,16933,16935,16942,16943,16948,16949,16954,16955]
def ridgeSupport928_006 : List Nat := [17041,17043,17047,17049,17053,17055,17089,17091,17095,17097,17101,17103,17386,17387,17388,17389,17390,17391,17398,17399,17400,17401,17402,17403,17674,17675,17676,17677,17678,17679,17686,17687]
def ridgeSupport928_007 : List Nat := [17688,17689,17690,17691,19991,19993,19995,20053,20055,20059,20061,20065,20067,20123,20125,20127,20185,20187,20191,20193,20197,20199,20440,20441,20442,20443,20444,20445,20471,20473,20475,20533]
def ridgeSupport928_008 : List Nat := [20535,20539,20541,20545,20547,20788,20789,20790,20791,20792,20793,21004,21005,21006,21007,21008,21009,21802,21803,21808,21809,21814,21815,21838,21839,21844,21845,21850,21851,21898,21899,21904]
def ridgeSupport928_009 : List Nat := [21905,21910,21911]
def ridgeSupport928_code : Nat := 0x1565eacb5591ab21562eac5555baab55556aaa554faa9d54dea9b5531aa6154aea955211a421483e907520da41944e689c5137a26d44d689a5043a08340f681dd037a06b3fee7fccff79fbb3f727edcfda9fb33f62773cee59dc33b7e76dced99d3f3a7674dce639cc3397672dce579cab386e70cce178a37146a28cc5188a2f145a287c50e8a1b1432285c50a87f70fea1fcc3f887ef0fda1f7c3ee87db0fb21f5c3ea859f0b36164c2c785870b0614fc29d85330a5e149c291847708ea11ac234845f08ba113c2258443087e10dc2198417082a102c20483ff07fa0f5c1ea83d307a20f3c1e683bf077a0eec1dc83b7076a05fc0bd817302de059c0b1811f0236044c08781070206015c02a804b009200fc01e802f0056008c00f80170025ffdbffa7feaffd1ff7bfee7f9eff35fe4bfc77f86ff05fcfbf9d7f32fe5dfc9bf917e76fce9f9abf347e5efcb9f93bf257e42fc7df8dbf197e16fc29f82bf047dfefbf9849b0926122c241847b08e610ec219842b0846106c209771aee25dc2bb8176faede5daebb5976aaed45da6bb496a2ad445a86b5096a0ad4059cab391671ace259c2b381642ac845906b209640ac805856b0a9614ac28584eb09960fac1e583ab07160dac1a551aaa31545aa8a5512aa21516aa2c5456a8a9514aa28539aa7314e5a9ca5392a7214c2a9845306a6094c0a980524aa491491a9225242a481462a8c45186a309460a8c00e7c1cf439e070c0e161c2834f869e0d3a16582ca8594
def ridgeSupport928_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport928_code
def ridgeSupport928_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport928_code
def ridgeSupport928_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport928_code
def ridgeSupport928_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport928_code
def ridgeSupport928_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport928_code
def ridgeSupport928_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport928_code
def ridgeSupport928_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport928_code
def ridgeSupport928_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport928_code
def ridgeSupport928_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport928_code
def ridgeSupport928_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport928_code
def ridgeSupport928_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport928_code
def ridgeSupport928_suffix_010 : List Nat := []
def ridgeSupport928_suffix_009 : List Nat := ridgeSupport928_009 ++ ridgeSupport928_suffix_010
def ridgeSupport928_suffix_008 : List Nat := ridgeSupport928_008 ++ ridgeSupport928_suffix_009
def ridgeSupport928_suffix_007 : List Nat := ridgeSupport928_007 ++ ridgeSupport928_suffix_008
def ridgeSupport928_suffix_006 : List Nat := ridgeSupport928_006 ++ ridgeSupport928_suffix_007
def ridgeSupport928_suffix_005 : List Nat := ridgeSupport928_005 ++ ridgeSupport928_suffix_006
def ridgeSupport928_suffix_004 : List Nat := ridgeSupport928_004 ++ ridgeSupport928_suffix_005
def ridgeSupport928_suffix_003 : List Nat := ridgeSupport928_003 ++ ridgeSupport928_suffix_004
def ridgeSupport928_suffix_002 : List Nat := ridgeSupport928_002 ++ ridgeSupport928_suffix_003
def ridgeSupport928_suffix_001 : List Nat := ridgeSupport928_001 ++ ridgeSupport928_suffix_002
def ridgeSupport928_suffix_000 : List Nat := ridgeSupport928_000 ++ ridgeSupport928_suffix_001
theorem ridgeSupport928_source : candidateRows 928 =
    (PackedRawNatGrowth.readList 15 291 ridgeSupport928_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
