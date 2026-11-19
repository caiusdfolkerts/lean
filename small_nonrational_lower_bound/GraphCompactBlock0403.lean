module
prelude
import GraphInputsRow27Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0403
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 114426986880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 247306748160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record001_result⟩)
 (.leaf ⟨(27, 256165052672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 256165117952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 256293011712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record004_result⟩)
 (.leaf ⟨(27, 264354431232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 264482390272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 264486551808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record007_result⟩)
 (.leaf ⟨(27, 264486617088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 265015034112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 265019260928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record010_result⟩)
 (.leaf ⟨(27, 265027584000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 268647301376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 384741507328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record013_result⟩)
 (.leaf ⟨(27, 389036458240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 476945875200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 593991139712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record016_result⟩)
 (.leaf ⟨(27, 665329958912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 680024637696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 680024702976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record019_result⟩)
 (.leaf ⟨(27, 680553120000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 680557346816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record021_result⟩)
 (.leaf ⟨(27, 680565669888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 697069289856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record023_result⟩)
 (.leaf ⟨(27, 728309530880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 736127648000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 736127713280), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record026_result⟩)
 (.leaf ⟨(27, 737304182784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 742368837632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 742897254656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record029_result⟩)
 (.leaf ⟨(27, 742901481472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 744317026560), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 744317091840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record032_result⟩)
 (.leaf ⟨(27, 744977629440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 744981856256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 746017816832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record035_result⟩)
 (.leaf ⟨(27, 751796519168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 751796584448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 751829549312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record038_result⟩)
 (.leaf ⟨(27, 752030916608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 776661401856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 793105235976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record041_result⟩)
 (.leaf ⟨(27, 799158649088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 814173290752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 814173356032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record044_result⟩)
 (.leaf ⟨(27, 814714191873), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 818334105600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record046_result⟩)
 (.leaf ⟨(27, 818874941441), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 819130794752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record048_result⟩)
 (.leaf ⟨(27, 819139183104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 873298231296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 873830875136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record051_result⟩)
 (.leaf ⟨(27, 874871062528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 956582330368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 989120725248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record054_result⟩)
 (.leaf ⟨(27, 998993133576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 999139885312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 1001017917696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record057_result⟩)
 (.leaf ⟨(27, 1025031307264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 1026566553856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 1026570585344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record060_result⟩)
 (.leaf ⟨(27, 1026711093249), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 1026843213825), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 1027111682048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record063_result⟩)
 (.leaf ⟨(27, 1208569921792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 1225749790720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 1226018193408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record066_result⟩)
 (.leaf ⟨(27, 1226026516480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 1232832921600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 1329502650624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record069_result⟩)
 (.leaf ⟨(27, 1363794886912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 1363794952192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record071_result⟩)
 (.leaf ⟨(27, 1363798918400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 1438984995072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record073_result⟩)
 (.leaf ⟨(27, 1458351669504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 1458351734784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 1479773618432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record076_result⟩)
 (.leaf ⟨(27, 1481920053504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 1481977724936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 1482109845512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record079_result⟩)
 (.leaf ⟨(27, 1482322657536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 1507602891008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 1507602956288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record082_result⟩)
 (.leaf ⟨(27, 1535621759232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 1654947660160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 1688082153856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record085_result⟩)
 (.leaf ⟨(27, 1688098668928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 1722844488064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 1857114177544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record088_result⟩)
 (.leaf ⟨(27, 1874294046720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 1876766491392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 1876774879744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record091_result⟩)
 (.leaf ⟨(27, 1890349842440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 1894626066440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 1912082531072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record094_result⟩)
 (.leaf ⟨(27, 1912090919424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 1919858902272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record096_result⟩)
 (.leaf ⟨(27, 1919858967552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 1920395641348), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record098_result⟩)
 (.leaf ⟨(27, 1920395771905), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00000.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17673 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 17673 17773 :=
  block_of_table results 17673 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0403
