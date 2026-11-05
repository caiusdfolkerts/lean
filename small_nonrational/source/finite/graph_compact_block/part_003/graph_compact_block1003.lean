module
prelude
import GraphInputsSix0Part00038Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1003
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 15129705975808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 15131975622912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record001_result⟩)
 (.leaf ⟨(32, 15136876167424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 15136880394240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 15136942227712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record004_result⟩)
 (.leaf ⟨(32, 15136953737216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 15138015445248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 15138027474944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record007_result⟩)
 (.leaf ⟨(32, 15166334829312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 15190498279680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 15191035150336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record010_result⟩)
 (.leaf ⟨(32, 15191043473408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 15196739404032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 15197012033536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record013_result⟩)
 (.leaf ⟨(32, 15197276274688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 15197284597760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 15197474455552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record016_result⟩)
 (.leaf ⟨(32, 15198316462080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 15212808798464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 15213579469344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record019_result⟩)
 (.leaf ⟨(32, 15213580001280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 15213919272960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record021_result⟩)
 (.leaf ⟨(32, 15214191837184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 15214654259200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record023_result⟩)
 (.leaf ⟨(32, 15214720319488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 15229975068928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 15230247698432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record026_result⟩)
 (.leaf ⟨(32, 15230511939584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 15230520262656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 15230759665664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record029_result⟩)
 (.leaf ⟨(32, 15247134064896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 15247939207680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 15247955984384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record032_result⟩)
 (.leaf ⟨(32, 15259083538688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 15259356168192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 15259620409344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record035_result⟩)
 (.leaf ⟨(32, 15259628732416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 15261163913472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 15261436542976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record038_result⟩)
 (.leaf ⟨(32, 15261700784128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 15261709107200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 15261898964992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record041_result⟩)
 (.leaf ⟨(32, 15262476730368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 15262740971520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 15262749294592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record044_result⟩)
 (.leaf ⟨(32, 15266001977344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 15266059714560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record046_result⟩)
 (.leaf ⟨(32, 15267042164736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 15268643406080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record048_result⟩)
 (.leaf ⟨(32, 15274046685440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 15274381213696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 15274587717632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record051_result⟩)
 (.leaf ⟨(32, 15277233307904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 15278004510720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 15285823275008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record054_result⟩)
 (.leaf ⟨(32, 15285897658368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 15286360080384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 15294399578368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record057_result⟩)
 (.leaf ⟨(32, 15294672207872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 15294936449024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 15294944772096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record060_result⟩)
 (.leaf ⟨(32, 15295184175104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 15299237642240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 15299344924672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record063_result⟩)
 (.leaf ⟨(32, 15302968672512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 15307282350336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 15307666423808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record066_result⟩)
 (.leaf ⟨(32, 15307823382528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 15309549404160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 15311558574336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record069_result⟩)
 (.leaf ⟨(32, 15312363717120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 15320148541440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record071_result⟩)
 (.leaf ⟨(32, 15320685346816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 15326611833088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record073_result⟩)
 (.leaf ⟨(32, 15326884462592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 15327148703744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 15327157026816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record076_result⟩)
 (.leaf ⟨(32, 15327396429824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 15333051138304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 15333588008960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record079_result⟩)
 (.leaf ⟨(32, 15333596332032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 15333637554176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 15335180927232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record082_result⟩)
 (.leaf ⟨(32, 15341641040128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 15341959053312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 15342182072320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record085_result⟩)
 (.leaf ⟨(32, 15342428758016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 15343770829056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 15344575971840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record088_result⟩)
 (.leaf ⟨(32, 15350213255424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 15403139039264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 15437534347520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record091_result⟩)
 (.leaf ⟨(32, 15471961186560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 15507386335488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 15507394723840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record094_result⟩)
 (.leaf ⟨(32, 15539485884448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 15540610416896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record096_result⟩)
 (.leaf ⟨(32, 15540678566144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 15549196157184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record098_result⟩)
 (.leaf ⟨(32, 15549264306432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00038.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30586 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30586 30686 :=
  block_of_table results 30586 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1003
