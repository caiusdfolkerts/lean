module
prelude
import GraphInputsRow25Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0290
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 41
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 40074576256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record000_result⟩)
 (.leaf ⟨(25, 44633768320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 47824585088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record002_result⟩)
 (.branch 4
 (.leaf ⟨(25, 109798719872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record003_result⟩)
 (.leaf ⟨(25, 109937000704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(25, 112228123008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record005_result⟩)
 (.leaf ⟨(25, 114229870848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record006_result⟩))
 (.branch 8
 (.leaf ⟨(25, 116647886880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record007_result⟩)
 (.branch 9
 (.leaf ⟨(25, 122815611136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record008_result⟩)
 (.leaf ⟨(25, 123090337920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(25, 156033433920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record010_result⟩)
 (.leaf ⟨(25, 156034474304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record011_result⟩))
 (.branch 13
 (.leaf ⟨(25, 191809814592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 624192225536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record013_result⟩)
 (.leaf ⟨(25, 624661987360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(25, 628485095680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record015_result⟩)
 (.leaf ⟨(25, 628822736928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record016_result⟩))
 (.branch 18
 (.leaf ⟨(25, 660095402240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record017_result⟩)
 (.branch 19
 (.leaf ⟨(25, 663987749120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record018_result⟩)
 (.leaf ⟨(25, 664256151808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(25, 664256217088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record020_result⟩)
 (.leaf ⟨(25, 696347304256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record021_result⟩))
 (.branch 23
 (.leaf ⟨(25, 706058699008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record022_result⟩)
 (.branch 24
 (.leaf ⟨(25, 706065039424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record023_result⟩)
 (.leaf ⟨(25, 732973531392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(25, 735053906176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record025_result⟩)
 (.leaf ⟨(25, 741295095808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record026_result⟩))
 (.branch 28
 (.leaf ⟨(25, 797525999872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record027_result⟩)
 (.branch 29
 (.leaf ⟨(25, 797534388224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record028_result⟩)
 (.leaf ⟨(25, 801686749440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(25, 801695137792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record030_result⟩)
 (.leaf ⟨(25, 805583257856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record031_result⟩))
 (.branch 33
 (.leaf ⟨(25, 806120128512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record032_result⟩)
 (.branch 34
 (.leaf ⟨(25, 810408771840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record033_result⟩)
 (.leaf ⟨(25, 814168998144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(25, 814705868800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record035_result⟩)
 (.branch 37
 (.leaf ⟨(25, 814714191872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record036_result⟩)
 (.leaf ⟨(25, 818329747712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(25, 818602377216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record038_result⟩)
 (.branch 40
 (.leaf ⟨(25, 818866618368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record039_result⟩)
 (.leaf ⟨(25, 818874941440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record040_result⟩)))))))
 (.branch 61
 (.branch 51
 (.branch 46
 (.branch 43
 (.branch 42
 (.leaf ⟨(25, 819139182592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record041_result⟩)
 (.leaf ⟨(25, 872562130944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record042_result⟩))
 (.branch 44
 (.leaf ⟨(25, 881286201472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 915645931648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record044_result⟩)
 (.leaf ⟨(25, 938857267456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record045_result⟩))))
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 938865655808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record046_result⟩)
 (.leaf ⟨(25, 1003281776896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 1003290165248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record048_result⟩)
 (.branch 50
 (.leaf ⟨(25, 1003682300160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record049_result⟩)
 (.leaf ⟨(25, 1007583035392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record050_result⟩)))))
 (.branch 56
 (.branch 53
 (.branch 52
 (.leaf ⟨(25, 1007843049728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record051_result⟩)
 (.leaf ⟨(25, 1016168775680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record052_result⟩))
 (.branch 54
 (.leaf ⟨(25, 1026566422784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record053_result⟩)
 (.branch 55
 (.leaf ⟨(25, 1026702770176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record054_result⟩)
 (.leaf ⟨(25, 1026711093248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record055_result⟩))))
 (.branch 58
 (.branch 57
 (.leaf ⟨(25, 1026843213824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record056_result⟩)
 (.leaf ⟨(25, 1042135679232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_result⟩))
 (.branch 59
 (.leaf ⟨(25, 1174210183424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record058_result⟩)
 (.branch 60
 (.leaf ⟨(25, 1174283583520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record059_result⟩)
 (.leaf ⟨(25, 1214009868544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record060_result⟩))))))
 (.branch 71
 (.branch 66
 (.branch 63
 (.branch 62
 (.leaf ⟨(25, 1255818756160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record061_result⟩)
 (.leaf ⟨(25, 1347147596032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record062_result⟩))
 (.branch 64
 (.leaf ⟨(25, 1364327464960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record063_result⟩)
 (.branch 65
 (.leaf ⟨(25, 1422317944832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record064_result⟩)
 (.leaf ⟨(25, 1484318114048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record065_result⟩))))
 (.branch 68
 (.branch 67
 (.leaf ⟨(25, 1507739107328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record066_result⟩)
 (.leaf ⟨(25, 1587196002560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record067_result⟩))
 (.branch 69
 (.leaf ⟨(25, 1689411191040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record068_result⟩)
 (.branch 70
 (.leaf ⟨(25, 1689679593728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record069_result⟩)
 (.leaf ⟨(25, 1689679659008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record070_result⟩)))))
 (.branch 76
 (.branch 73
 (.branch 72
 (.leaf ⟨(25, 1693972463872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record071_result⟩)
 (.leaf ⟨(25, 1697195757824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record072_result⟩))
 (.branch 74
 (.leaf ⟨(25, 1702289801472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record073_result⟩)
 (.branch 75
 (.leaf ⟨(25, 1702293963008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record074_result⟩)
 (.leaf ⟨(25, 1702294028288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record075_result⟩))))
 (.branch 79
 (.branch 77
 (.leaf ⟨(25, 1723972223232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record076_result⟩)
 (.branch 78
 (.leaf ⟨(25, 1723972288512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record077_result⟩)
 (.leaf ⟨(25, 1725247262976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record078_result⟩)))
 (.branch 80
 (.leaf ⟨(25, 1727864570112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record079_result⟩)
 (.branch 81
 (.leaf ⟨(25, 1728265093376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record080_result⟩)
 (.leaf ⟨(25, 1728265158656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record081_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12130 + i))) 0 82 :=
  interval_of_check _ 0 82 (by decide +kernel)

public theorem complete : Block 12130 12212 :=
  block_of_table results 12130 82 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0290
