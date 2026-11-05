module
prelude
import GraphInputsRow27Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0417
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 31819361681408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 31819551539200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record001_result⟩)
 (.leaf ⟨(27, 31819559862272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 31819601084416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 31820070789120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record004_result⟩)
 (.leaf ⟨(27, 31890426368032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 31890690609184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 31994901692416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record007_result⟩)
 (.leaf ⟨(27, 32011536367616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 32011808931840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 32012271353856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record010_result⟩)
 (.leaf ⟨(27, 32012337414144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 32025986732096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 32027077263360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record013_result⟩)
 (.leaf ⟨(27, 32043780079616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 32044316884992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 32059272740864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record016_result⟩)
 (.leaf ⟨(27, 32076512362496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 32078179729408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 32078574010368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record019_result⟩)
 (.leaf ⟨(27, 32163421491264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 32164039131392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record021_result⟩)
 (.leaf ⟨(27, 32164049600512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 32164247781376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record023_result⟩)
 (.leaf ⟨(27, 32172629098496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 32196245078016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 32196443258880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record026_result⟩)
 (.leaf ⟨(27, 32200649146368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 32204220022784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 32221985652736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record029_result⟩)
 (.leaf ⟨(27, 32232861401088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 32232869724160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 32266105389056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record032_result⟩)
 (.leaf ⟨(27, 32299321147392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 32300856786944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 32332606357504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record035_result⟩)
 (.leaf ⟨(27, 32333118048320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 32335198292032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 32335214936640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record038_result⟩)
 (.leaf ⟨(27, 32439497920512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 32441544744960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 32454423355392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record041_result⟩)
 (.leaf ⟨(27, 32457873690656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 32474541916160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 32492232901136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record044_result⟩)
 (.leaf ⟨(27, 32507026214912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 32513464999936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record046_result⟩)
 (.leaf ⟨(27, 32514521571328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 32514547712000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record048_result⟩)
 (.leaf ⟨(27, 32522297937952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 32531727515648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 32643379953664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record051_result⟩)
 (.leaf ⟨(27, 32643388276736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 32658948628736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 32659032309760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record054_result⟩)
 (.leaf ⟨(27, 32659485499392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 32659486539776), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 32659502014464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record057_result⟩)
 (.leaf ⟨(27, 32676673486848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 32693828061184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 32712781991936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record060_result⟩)
 (.leaf ⟨(27, 32713178353664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 32715051639040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 32715060547584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record063_result⟩)
 (.leaf ⟨(27, 32715324788736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 32725001043968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 32728053714976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record066_result⟩)
 (.leaf ⟨(27, 32748190367744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 32780360613888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 32780550471680), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record069_result⟩)
 (.leaf ⟨(27, 32780558794752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 32781069721600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record071_result⟩)
 (.leaf ⟨(27, 32783216935424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 32787797647616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record073_result⟩)
 (.leaf ⟨(27, 32787881328640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 32788334518272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 32788335558656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record076_result⟩)
 (.leaf ⟨(27, 32788351033344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 32804960342048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 32804977516544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record079_result⟩)
 (.leaf ⟨(27, 32805011587072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 32806034087936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 32806101188608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record082_result⟩)
 (.leaf ⟨(27, 32813844004864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 32814355712000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 32822677080064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record085_result⟩)
 (.leaf ⟨(27, 32839319945732), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 32916646404352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 32916713570304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record088_result⟩)
 (.leaf ⟨(27, 32916721893376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 32917183275008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 32917233600512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record091_result⟩)
 (.leaf ⟨(27, 32918776973568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 32919313844224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 32919330488832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record094_result⟩)
 (.leaf ⟨(27, 32933809358880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 32935956709892), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record096_result⟩)
 (.leaf ⟨(27, 33022146003200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 33098495492096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record098_result⟩)
 (.leaf ⟨(27, 33102730625024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00014.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19073 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19073 19173 :=
  block_of_table results 19073 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0417
