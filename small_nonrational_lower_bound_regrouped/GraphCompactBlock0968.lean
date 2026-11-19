module
prelude
import GraphInputsSix0Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0968
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 1481920053504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 1481977724936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record001_result⟩)
 (.leaf ⟨(32, 1482109845512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 1482322657536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 1482374086664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record004_result⟩)
 (.leaf ⟨(32, 1484326502656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 1484594905344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 1484594970624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record007_result⟩)
 (.leaf ⟨(32, 1488887775488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 1490968150272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 1497477709952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record010_result⟩)
 (.leaf ⟨(32, 1501365798144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 1501497983232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 1501506371584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record013_result⟩)
 (.leaf ⟨(32, 1501766385920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 1501774774272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 1501898506496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record016_result⟩)
 (.leaf ⟨(32, 1502034853888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 1502043176960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 1505522516224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record019_result⟩)
 (.leaf ⟨(32, 1506067644416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 1507602891008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record021_result⟩)
 (.leaf ⟨(32, 1507602956288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 1507739107584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record023_result⟩)
 (.leaf ⟨(32, 1507747495936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 1508148019200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 1535621759232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record026_result⟩)
 (.leaf ⟨(32, 1553312284928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 1587604914432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 1652667023744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record029_result⟩)
 (.leaf ⟨(32, 1653065466240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 1654813458816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 1654947660160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record032_result⟩)
 (.leaf ⟨(32, 1655209820544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 1655211901312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 1655216062848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record035_result⟩)
 (.leaf ⟨(32, 1668094673280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 1668100964544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 1688082153856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record038_result⟩)
 (.leaf ⟨(32, 1688098668928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 1688216355200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 1688232870272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record041_result⟩)
 (.leaf ⟨(32, 1688484757888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 1689541329280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 1689679659264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record044_result⟩)
 (.leaf ⟨(32, 1701369659584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 1702294028544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record046_result⟩)
 (.leaf ⟨(32, 1702562463872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 1705785786384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record048_result⟩)
 (.leaf ⟨(32, 1722576085376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 1722844488064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 1723972288768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record051_result⟩)
 (.leaf ⟨(32, 1727139438976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 1727139487936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 1728196010368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record054_result⟩)
 (.leaf ⟨(32, 1728196059328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 1728265158912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 1735729389760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record057_result⟩)
 (.leaf ⟨(32, 1736454537472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 1736586658048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 1736652718336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record060_result⟩)
 (.leaf ⟨(32, 1736855093376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 1737998041104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 1766049513728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record063_result⟩)
 (.leaf ⟨(32, 1774639415552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 1774639480832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 1778934366464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record066_result⟩)
 (.leaf ⟨(32, 1791161344384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 1805574553728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 1834634772736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record069_result⟩)
 (.leaf ⟨(32, 1843224674560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 1843224739840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record071_result⟩)
 (.leaf ⟨(32, 1843358875904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 1856594084096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record073_result⟩)
 (.leaf ⟨(32, 1857056506112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 1857114177544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 1859330834688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record076_result⟩)
 (.leaf ⟨(32, 1868994511104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 1872716988424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 1873161011456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record079_result⟩)
 (.leaf ⟨(32, 1874293981440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 1874294046720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 1876238074112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record082_result⟩)
 (.leaf ⟨(32, 1876502315264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 1876510703616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 1876766491392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record085_result⟩)
 (.leaf ⟨(32, 1876774879744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 1876774944768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 1877584412928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record088_result⟩)
 (.leaf ⟨(32, 1877584478208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 1889945354496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 1890347958528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record091_result⟩)
 (.leaf ⟨(32, 1890349842440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 1894357600512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 1894374245120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record094_result⟩)
 (.leaf ⟨(32, 1894626066440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 1894646874368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record096_result⟩)
 (.leaf ⟨(32, 1903484272896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 1907108315144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record098_result⟩)
 (.leaf ⟨(32, 1907510919176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00003.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27086 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27086 27186 :=
  block_of_table results 27086 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0968
