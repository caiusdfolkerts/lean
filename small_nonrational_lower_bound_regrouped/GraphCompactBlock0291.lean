module
prelude
import GraphInputsRow25Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0291
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 1729408012544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 1736454537216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record001_result⟩)
 (.leaf ⟨(25, 1736586592512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 1736586657792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 1736850898944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record004_result⟩)
 (.leaf ⟨(25, 1737729511680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 1774639382529), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 1805171851520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record007_result⟩)
 (.leaf ⟨(25, 1859322446080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(25, 1859330834432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record009_result⟩)
 (.branch 11
 (.leaf ⟨(25, 1861402820864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record010_result⟩)
 (.leaf ⟨(25, 1874285592832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(25, 1875436961792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 1876774879232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record013_result⟩)
 (.leaf ⟨(25, 1877718663168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(25, 1894646874112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 1894886211840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record016_result⟩)
 (.leaf ⟨(25, 1907521257728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(25, 1907525484544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 1907649153024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record019_result⟩)
 (.leaf ⟨(25, 1912065753856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(25, 1912090918912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record021_result⟩)
 (.leaf ⟨(25, 1919850578176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(25, 1920387448832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record023_result⟩)
 (.leaf ⟨(25, 1920395771904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(25, 1972073660417), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record025_result⟩)
 (.branch 27
 (.leaf ⟨(25, 1980663627776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record026_result⟩)
 (.leaf ⟨(25, 1980787360000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(25, 1996492964096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(25, 1996501352448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record029_result⟩)
 (.leaf ⟨(25, 1996893487360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(25, 1999621914624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 2002940657664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record032_result⟩)
 (.leaf ⟨(25, 2003134611712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(25, 2004013875200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 2004174799104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record035_result⟩)
 (.leaf ⟨(25, 2015157551105), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(25, 2019442065664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record037_result⟩)
 (.branch 39
 (.leaf ⟨(25, 2019452518401), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record038_result⟩)
 (.leaf ⟨(25, 2019452534784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(25, 2019777609984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record040_result⟩)
 (.branch 42
 (.leaf ⟨(25, 2019913957376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record041_result⟩)
 (.leaf ⟨(25, 2019922280448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(25, 2020318642176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 2031817392128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record044_result⟩)
 (.leaf ⟨(25, 2032325132544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 2032337422336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record046_result⟩)
 (.leaf ⟨(25, 2036370276608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 2036374503424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record048_result⟩)
 (.leaf ⟨(25, 2036498171904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(25, 2040914772736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record050_result⟩)
 (.branch 52
 (.leaf ⟨(25, 2049517289472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record051_result⟩)
 (.leaf ⟨(25, 2057289498880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(25, 2057557966848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record053_result⟩)
 (.branch 55
 (.leaf ⟨(25, 2057566289920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record054_result⟩)
 (.leaf ⟨(25, 2058094641664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(25, 2058103029760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record056_result⟩)
 (.branch 58
 (.leaf ⟨(25, 2100910391552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record057_result⟩)
 (.leaf ⟨(25, 2118094225408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(25, 2132606517504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record059_result⟩)
 (.branch 61
 (.leaf ⟨(25, 2132614905856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record060_result⟩)
 (.leaf ⟨(25, 2132854243584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(25, 2133007040768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record062_result⟩)
 (.branch 64
 (.leaf ⟨(25, 2133011267584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record063_result⟩)
 (.leaf ⟨(25, 2133122646272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(25, 2133134936064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record065_result⟩)
 (.branch 67
 (.leaf ⟨(25, 2137551536896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record066_result⟩)
 (.leaf ⟨(25, 2143792661248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(25, 2147697559552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record068_result⟩)
 (.branch 70
 (.leaf ⟨(25, 2147895740416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record069_result⟩)
 (.leaf ⟨(25, 2149769609472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(25, 2150306480128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record071_result⟩)
 (.leaf ⟨(25, 2150314803200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record072_result⟩))
 (.branch 74
 (.leaf ⟨(25, 2446399176704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record073_result⟩)
 (.leaf ⟨(25, 2454712287488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(25, 2455249158144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record075_result⟩)
 (.branch 77
 (.leaf ⟨(25, 2455257481216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record076_result⟩)
 (.leaf ⟨(25, 2459277787136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(25, 2521559040000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record078_result⟩)
 (.branch 80
 (.leaf ⟨(25, 2521829490816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record079_result⟩)
 (.leaf ⟨(25, 2588126806016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(25, 2686843944960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record081_result⟩)
 (.branch 83
 (.leaf ⟨(25, 2793211494656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record082_result⟩)
 (.leaf ⟨(25, 2796438950144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(25, 2828651204864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record084_result⟩)
 (.branch 86
 (.leaf ⟨(25, 2905954324736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record085_result⟩)
 (.leaf ⟨(25, 2968439029760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(25, 2974948556800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record087_result⟩)
 (.branch 89
 (.leaf ⟨(25, 2975072289024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record088_result⟩)
 (.leaf ⟨(25, 3034803343616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(25, 3080298987648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record090_result⟩)
 (.branch 92
 (.leaf ⟨(25, 3102382030848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record091_result⟩)
 (.leaf ⟨(25, 3135617695744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(25, 3140430659584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record093_result⟩)
 (.branch 95
 (.leaf ⟨(25, 3140438982656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record094_result⟩)
 (.leaf ⟨(25, 3149020561408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(25, 3152644440320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record096_result⟩)
 (.leaf ⟨(25, 3153313431552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record097_result⟩))
 (.branch 99
 (.leaf ⟨(25, 3157073657856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record098_result⟩)
 (.leaf ⟨(25, 3157610463232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00001.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12212 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 12212 12312 :=
  block_of_table results 12212 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0291
