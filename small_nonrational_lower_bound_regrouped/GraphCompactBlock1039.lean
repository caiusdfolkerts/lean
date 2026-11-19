module
prelude
import GraphInputsSix0Part00074Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1039
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 28273804378112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 28273878761472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record001_result⟩)
 (.leaf ⟨(32, 28274341183488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 28282380681472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 28282653310976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record004_result⟩)
 (.leaf ⟨(32, 28282917552128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 28282925875200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 28283165278208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record007_result⟩)
 (.leaf ⟨(32, 28290949775616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 28295263453440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 28295647526912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record010_result⟩)
 (.leaf ⟨(32, 28295804485632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 28297530507264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 28299539677440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record013_result⟩)
 (.leaf ⟨(32, 28300344820224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 28308129644544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 28308666449920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record016_result⟩)
 (.leaf ⟨(32, 28314863407360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 28321309003840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 28325712503040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record019_result⟩)
 (.leaf ⟨(32, 28360071709440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 28391211335680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record021_result⟩)
 (.leaf ⟨(32, 28424496545792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 28451027353600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record023_result⟩)
 (.leaf ⟨(32, 28451231776768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 28451272933632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 28451283142656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record026_result⟩)
 (.leaf ⟨(32, 28452298752000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 28452304994304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 28452313121024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record029_result⟩)
 (.leaf ⟨(32, 28452323330048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 28453487248128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 28458554245376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record032_result⟩)
 (.leaf ⟨(32, 28458564454400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 28484378624000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 28484508598528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record035_result⟩)
 (.leaf ⟨(32, 28484518807552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 28484626024704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 28488786643200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record038_result⟩)
 (.leaf ⟨(32, 28488803287808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 28492955781120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 28493484130824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record041_result⟩)
 (.leaf ⟨(32, 28521133309952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 28523164139520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 28523213684736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record044_result⟩)
 (.leaf ⟨(32, 28531467886848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 28590630551808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record046_result⟩)
 (.leaf ⟨(32, 28590630584448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 28590694563968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record048_result⟩)
 (.leaf ⟨(32, 28590696612096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 28590696644736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 28590731264016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record051_result⟩)
 (.leaf ⟨(32, 28590828765312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 28591097168000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 28597170569232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record054_result⟩)
 (.leaf ⟨(32, 28597539594368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 28605762551824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 28623963259008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record057_result⟩)
 (.leaf ⟨(32, 28623965307136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 28623965339776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 28623966928912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record060_result⟩)
 (.leaf ⟨(32, 28623969501312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 28624369532944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 28625019830400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record063_result⟩)
 (.leaf ⟨(32, 28625021878528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 28626245484560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 28626251178112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record066_result⟩)
 (.leaf ⟨(32, 28626515968016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 28631667589376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 28632808427776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record069_result⟩)
 (.leaf ⟨(32, 28636192194688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 28644513693824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record071_result⟩)
 (.leaf ⟨(32, 28658257969280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 28658259558416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record073_result⟩)
 (.leaf ⟨(32, 28658262130816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 28666026279168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 28666094428416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record076_result⟩)
 (.leaf ⟨(32, 28701527965696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 28716202737792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 28717292339328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record079_result⟩)
 (.leaf ⟨(32, 28717294452736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 28717298484224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 28717426410112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record082_result⟩)
 (.leaf ⟨(32, 28727042998288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 28727048691840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 28731525566720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record085_result⟩)
 (.leaf ⟨(32, 28734611538176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 28764811624448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 28769168408832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record088_result⟩)
 (.leaf ⟨(32, 28773397364736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 28781718962176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 28781850919552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record091_result⟩)
 (.leaf ⟨(32, 28794627833984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 28795701051520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 28796163473536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record094_result⟩)
 (.leaf ⟨(32, 28806749364480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 28813929103488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record096_result⟩)
 (.leaf ⟨(32, 28813935248384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 28827906769152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record098_result⟩)
 (.leaf ⟨(32, 28827906834432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00074.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34013 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 34013 34113 :=
  block_of_table results 34013 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1039
