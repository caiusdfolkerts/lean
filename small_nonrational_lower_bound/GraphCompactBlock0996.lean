module
prelude
import GraphInputsSix0Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0996
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 11958551150592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 11958553231360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record001_result⟩)
 (.leaf ⟨(32, 11958557360256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 11958604531968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 11958608726144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record004_result⟩)
 (.leaf ⟨(32, 11958819520640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 11958821601408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 11958821634048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record007_result⟩)
 (.leaf ⟨(32, 11960825413633), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 11963945975809), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 11965885843712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record010_result⟩)
 (.leaf ⟨(32, 11965890037888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 11965984934144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 11966065754112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record013_result⟩)
 (.leaf ⟨(32, 11966334124160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 11966334156800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 11966335717376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record016_result⟩)
 (.leaf ⟨(32, 11967194529792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 11967198658561), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 11974475778176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record019_result⟩)
 (.leaf ⟨(32, 11974574868608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 11983010152576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record021_result⟩)
 (.leaf ⟨(32, 11983012265984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 11983045296128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record023_result⟩)
 (.leaf ⟨(32, 11984099754112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 11984101867520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 11984105899008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record026_result⟩)
 (.leaf ⟨(32, 11984233824896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 11984304079872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 11991704174848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record029_result⟩)
 (.leaf ⟨(32, 11991704240128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 11991708369024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 11991712270464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record032_result⟩)
 (.leaf ⟨(32, 11991838441472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 11991840196864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 11991842570368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record035_result⟩)
 (.leaf ⟨(32, 11991842603008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 11991844391040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 11991963928584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record038_result⟩)
 (.leaf ⟨(32, 11992108632192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 11996116420864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 11996116486144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record041_result⟩)
 (.leaf ⟨(32, 11996120615040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 11996124677128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 11996141453313), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record044_result⟩)
 (.leaf ⟨(32, 12000277170432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 12000277235712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record046_result⟩)
 (.leaf ⟨(32, 12000281364608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 12000417547272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record048_result⟩)
 (.leaf ⟨(32, 12000430194688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 12000434323457), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 12000681788424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record051_result⟩)
 (.leaf ⟨(32, 12000698564609), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 12008867104896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 12021613593728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record054_result⟩)
 (.leaf ⟨(32, 12021617787904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 12021881897476), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 12098023293184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record057_result⟩)
 (.leaf ⟨(32, 12098027487360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 12098157494528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 12098161688704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record060_result⟩)
 (.leaf ⟨(32, 12098262368272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 12098425897216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 12098425929856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record063_result⟩)
 (.leaf ⟨(32, 12100169728256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 12100173922432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 12100210622480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record066_result⟩)
 (.leaf ⟨(32, 12100301848832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 12100303929600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 12100304969984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record069_result⟩)
 (.leaf ⟨(32, 12100308123776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 12100342743056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record071_result⟩)
 (.leaf ⟨(32, 12100408803344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 12100570284160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record073_result⟩)
 (.leaf ⟨(32, 12100572332288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 12100572364928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 12100573405312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record076_result⟩)
 (.leaf ⟨(32, 12104503492624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 12104596799744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 12104637693968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record079_result⟩)
 (.leaf ⟨(32, 12104703754256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 12104865202432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 12104865235072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record082_result⟩)
 (.leaf ⟨(32, 12113089232912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 12113223434256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 12113290534928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record085_result⟩)
 (.leaf ⟨(32, 12113455136896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 12133438423296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 12133442617472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record088_result⟩)
 (.leaf ⟨(32, 12133446287376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 12133454938368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 12133572624640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record091_result⟩)
 (.leaf ⟨(32, 12133576786176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 12133576818816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 12133578407952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record094_result⟩)
 (.leaf ⟨(32, 12133842649104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 12133845221504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record096_result⟩)
 (.leaf ⟨(32, 12134629196032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 12134901792896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record098_result⟩)
 (.leaf ⟨(32, 12137873358864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00031.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29886 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29886 29986 :=
  block_of_table results 29886 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0996
