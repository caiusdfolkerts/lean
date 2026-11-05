module
prelude
import GraphInputsSix0Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0988
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 8186764525568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 8186770767872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record001_result⟩)
 (.leaf ⟨(32, 8186811924736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 8186822133760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 8189026239232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record004_result⟩)
 (.leaf ⟨(32, 8194999222528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 8195011512320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 8195133423872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record007_result⟩)
 (.leaf ⟨(32, 8195143632896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 8195356508160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 8195407874048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record010_result⟩)
 (.leaf ⟨(32, 8195603177536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 8197347738368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 8197750391360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record013_result⟩)
 (.leaf ⟨(32, 8246388408704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 8246389969280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 8246396260544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record016_result⟩)
 (.leaf ⟨(32, 8246492729616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 8246492989712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 8247463445376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record019_result⟩)
 (.leaf ⟨(32, 8247471866112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 8247549561104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record021_result⟩)
 (.leaf ⟨(32, 8247553722640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 8247570956544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record023_result⟩)
 (.leaf ⟨(32, 8247956359312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 8247973560576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 8247973593216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record026_result⟩)
 (.leaf ⟨(32, 8247975182352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 8250926371072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 8250942886144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record029_result⟩)
 (.leaf ⟨(32, 8251194806400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 8251194834960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 8252016362240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record032_result⟩)
 (.leaf ⟨(32, 8252020556032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 8252251377792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 8252251406352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record035_result⟩)
 (.leaf ⟨(32, 8252288958720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 8252289024000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 8252523811072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record038_result⟩)
 (.leaf ⟨(32, 8256313426176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 8256577667328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 8256581828864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record041_result⟩)
 (.leaf ⟨(32, 8256581894144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 8256583909632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 8256684560640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record044_result⟩)
 (.leaf ⟨(32, 8264079687696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 8265006059776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record046_result⟩)
 (.leaf ⟨(32, 8265167569152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 8265167634432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record048_result⟩)
 (.leaf ⟨(32, 8265408712768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 8268629938192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 8315619082256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record051_result⟩)
 (.leaf ⟨(32, 8321234960640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 8321243348992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 8323940811008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record054_result⟩)
 (.leaf ⟨(32, 8324192077840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 8324205052160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 8324209213696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record057_result⟩)
 (.leaf ⟨(32, 8324209278976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 8324212855040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 8325131469056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record060_result⟩)
 (.leaf ⟨(32, 8325395710208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 8325404098560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 8328747483392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record063_result⟩)
 (.leaf ⟨(32, 8332794953984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 8332795019264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 8333054445584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record066_result⟩)
 (.leaf ⟨(32, 8333717209344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 8333725597696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 8334117732608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record069_result⟩)
 (.leaf ⟨(32, 8334128185345), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 8337337385216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record071_result⟩)
 (.leaf ⟨(32, 8337349414912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 8362578215168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record073_result⟩)
 (.leaf ⟨(32, 8363115085824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 8371163955456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 8371700826112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record076_result⟩)
 (.leaf ⟨(32, 8371709149184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 8375324705024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 8388637364480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record079_result⟩)
 (.leaf ⟨(32, 8392928674048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 8392928739328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 8392930234624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record082_result⟩)
 (.leaf ⟨(32, 8393985245440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 8393985310720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 8401515974912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record085_result⟩)
 (.leaf ⟨(32, 8401518641152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 8401522266176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 8401639704592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record088_result⟩)
 (.leaf ⟨(32, 8402713444353), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 8405922644224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 8440286085120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record091_result⟩)
 (.leaf ⟨(32, 8474775782144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 8491427234048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 8500285603840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record094_result⟩)
 (.leaf ⟨(32, 8508607102976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 8509143908352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record096_result⟩)
 (.leaf ⟨(32, 8517465407488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 8521374859280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record098_result⟩)
 (.leaf ⟨(32, 8521777463312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00023.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29086 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29086 29186 :=
  block_of_table results 29086 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0988
