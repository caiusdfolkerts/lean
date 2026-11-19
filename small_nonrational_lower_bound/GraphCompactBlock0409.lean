module
prelude
import GraphInputsRow27Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0409
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 14623568823296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 14623826919552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record001_result⟩)
 (.leaf ⟨(27, 14623833064448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 14623960990336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 14630606864384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record004_result⟩)
 (.leaf ⟨(27, 14699936612352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 14702016987136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 14702479409152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record007_result⟩)
 (.leaf ⟨(27, 14716245131264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 14749480796160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 14768387784704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record010_result⟩)
 (.leaf ⟨(27, 14781746511872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 14786039382016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 14794625122304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record013_result⟩)
 (.leaf ⟨(27, 14805357297664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 14999783219200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 15191035150336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record016_result⟩)
 (.leaf ⟨(27, 15191043473408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 15197284597760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 15197474455552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record019_result⟩)
 (.leaf ⟨(27, 15213580001280), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 15213919272960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record021_result⟩)
 (.leaf ⟨(27, 15214191837184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 15214654259200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record023_result⟩)
 (.leaf ⟨(27, 15214720319488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 15230520262656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 15247955984384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record026_result⟩)
 (.leaf ⟨(27, 15259620409344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 15259628732416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 15266001977344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record029_result⟩)
 (.leaf ⟨(27, 15267042164736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 15285897658368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 15286360080384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record032_result⟩)
 (.leaf ⟨(27, 15299237642240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 15320685346816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 15327148703744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record035_result⟩)
 (.leaf ⟨(27, 15327157026816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 15333588008960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 15333596332032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record038_result⟩)
 (.leaf ⟨(27, 15342182072320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 15342428758016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 15592142733312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record041_result⟩)
 (.leaf ⟨(27, 15645102047232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 15664089661440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 15703764713472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record044_result⟩)
 (.leaf ⟨(27, 15712410140673), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 15839927812096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record046_result⟩)
 (.leaf ⟨(27, 15840185419784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 15842265793544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record048_result⟩)
 (.leaf ⟨(27, 15842282569729), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 16159357272064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 16176264511488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record051_result⟩)
 (.leaf ⟨(27, 16365302906880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 16432880746496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 16492760699152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record054_result⟩)
 (.leaf ⟨(27, 16493817530640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 16494981877888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 16502649602048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record057_result⟩)
 (.leaf ⟨(27, 16532679852288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 16532679917568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 16536182538240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record060_result⟩)
 (.leaf ⟨(27, 16639265873984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 16639265890304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 16639317772304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record063_result⟩)
 (.leaf ⟨(27, 16648780128256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 16657528406016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 16721452793856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record066_result⟩)
 (.leaf ⟨(27, 16721725358080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 16722187780096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 16729469091840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record069_result⟩)
 (.leaf ⟨(27, 16757091729408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 16776211662864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record071_result⟩)
 (.leaf ⟨(27, 16777519055104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 16846339244032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record073_result⟩)
 (.leaf ⟨(27, 16881779998720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 16914135392320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 16914136449024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record076_result⟩)
 (.leaf ⟨(27, 16930778390592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 16930812477440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 16930814558208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record079_result⟩)
 (.leaf ⟨(27, 16931904159744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 16943922939904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 16969415787012), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record082_result⟩)
 (.leaf ⟨(27, 16969415918592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 16976013492224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 16976021815296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record085_result⟩)
 (.leaf ⟨(27, 16976153935872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 16978300370944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 16982857482240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record088_result⟩)
 (.leaf ⟨(27, 17003842764800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 17010356453376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 17042447698192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record091_result⟩)
 (.leaf ⟨(27, 17042481381633), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 17042489282688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 17042724163600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record094_result⟩)
 (.leaf ⟨(27, 17043780995088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 17043798196224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record096_result⟩)
 (.leaf ⟨(27, 17051578601472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 17052406448128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record098_result⟩)
 (.leaf ⟨(27, 17052676915201), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00006.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18273 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18273 18373 :=
  block_of_table results 18273 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0409
