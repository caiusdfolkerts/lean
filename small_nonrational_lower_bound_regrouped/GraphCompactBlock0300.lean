module
prelude
import GraphInputsRow25Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0300
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 12650067066880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 12650327081216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record001_result⟩)
 (.leaf ⟨(25, 12650335469568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 12650558292224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 12650570321920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record004_result⟩)
 (.leaf ⟨(25, 12653261492480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 12654359937024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 12654624178176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record007_result⟩)
 (.leaf ⟨(25, 12654628339712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(25, 12654719041792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record009_result⟩)
 (.branch 11
 (.leaf ⟨(25, 12654731071488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record010_result⟩)
 (.leaf ⟨(25, 12658074456320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(25, 12663040540928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 12663052570624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record013_result⟩)
 (.leaf ⟨(25, 12663209885824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(25, 12663214080000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 12663308976256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record016_result⟩)
 (.leaf ⟨(25, 12663443177600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(25, 12666664390784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 12713392869632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record019_result⟩)
 (.leaf ⟨(25, 12722247336192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(25, 12722255724544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record021_result⟩)
 (.leaf ⟨(25, 12722259365888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record022_result⟩))
 (.branch 24
 (.leaf ⟨(25, 12722498703616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record023_result⟩)
 (.leaf ⟨(25, 12723312295936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(25, 12723572179712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record025_result⟩)
 (.branch 27
 (.leaf ⟨(25, 12730837270656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record026_result⟩)
 (.leaf ⟨(25, 12731088638080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(25, 12732162114176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record028_result⟩)
 (.branch 30
 (.leaf ⟨(25, 12739678306832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record029_result⟩)
 (.leaf ⟨(25, 12781978128640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(25, 12786411831296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 12786683875328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record032_result⟩)
 (.leaf ⟨(25, 12790976745472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(25, 12791083962624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 12795513470976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record035_result⟩)
 (.leaf ⟨(25, 12799562485760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(25, 12800478937856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record037_result⟩)
 (.branch 39
 (.leaf ⟨(25, 12800747373184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record038_result⟩)
 (.leaf ⟨(25, 12804102816272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(25, 12864240746496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record040_result⟩)
 (.branch 42
 (.leaf ⟨(25, 12923854393344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record041_result⟩)
 (.leaf ⟨(25, 12924110798976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(25, 12928405749888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 12928411504640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record044_result⟩)
 (.leaf ⟨(25, 12932951835152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 12936844415104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record046_result⟩)
 (.leaf ⟨(25, 12937917891200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 13125437128960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record048_result⟩)
 (.leaf ⟨(25, 13125705596928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(25, 13125713920000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record050_result⟩)
 (.branch 52
 (.leaf ⟨(25, 13125973999616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record051_result⟩)
 (.leaf ⟨(25, 13126225627136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(25, 13134010124544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record053_result⟩)
 (.branch 55
 (.leaf ⟨(25, 13134303592448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record054_result⟩)
 (.leaf ⟨(25, 13134546995200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(25, 13134563639808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record056_result⟩)
 (.branch 58
 (.leaf ⟨(25, 13142600059008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record057_result⟩)
 (.leaf ⟨(25, 13151189860868), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(25, 13197668073728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record059_result⟩)
 (.branch 61
 (.leaf ⟨(25, 13199815549184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record060_result⟩)
 (.leaf ⟨(25, 13199819767840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(25, 13200888766720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record062_result⟩)
 (.branch 64
 (.leaf ⟨(25, 13204114718752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record063_result⟩)
 (.leaf ⟨(25, 13204376879136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(25, 13204378959904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record065_result⟩)
 (.branch 67
 (.leaf ⟨(25, 13233084244224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record066_result⟩)
 (.leaf ⟨(25, 13237377114368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(25, 13237645517056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record068_result⟩)
 (.branch 70
 (.leaf ⟨(25, 13237645574176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record069_result⟩)
 (.leaf ⟨(25, 13237647654944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(25, 13238777511936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record071_result⟩)
 (.leaf ⟨(25, 13271743143968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record072_result⟩))
 (.branch 74
 (.leaf ⟨(25, 13272007385120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record073_result⟩)
 (.leaf ⟨(25, 13273136201728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(25, 13281726070912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record075_result⟩)
 (.branch 77
 (.leaf ⟨(25, 13314961735808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record076_result⟩)
 (.leaf ⟨(25, 13338600833280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(25, 13338600898560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record078_result⟩)
 (.branch 80
 (.leaf ⟨(25, 13340731007008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record079_result⟩)
 (.leaf ⟨(25, 13342895849472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(25, 13350445531264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record081_result⟩)
 (.branch 83
 (.leaf ⟨(25, 13350445563904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record082_result⟩)
 (.leaf ⟨(25, 13350446571648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(25, 13350515777568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record084_result⟩)
 (.branch 86
 (.leaf ⟨(25, 13351589515296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record085_result⟩)
 (.leaf ⟨(25, 13377221115904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(25, 13377359380480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record087_result⟩)
 (.branch 89
 (.leaf ⟨(25, 13383682236544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record088_result⟩)
 (.leaf ⟨(25, 13385949249537), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(25, 13523310641280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record090_result⟩)
 (.branch 92
 (.leaf ⟨(25, 13660749594624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record091_result⟩)
 (.leaf ⟨(25, 13745263312928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(25, 13752779477024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record093_result⟩)
 (.branch 95
 (.leaf ⟨(25, 13753043718176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record094_result⟩)
 (.leaf ⟨(25, 13762731974784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(25, 13890486804736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record096_result⟩)
 (.leaf ⟨(25, 13890486870016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record097_result⟩))
 (.branch 99
 (.leaf ⟨(25, 13899076739200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record098_result⟩)
 (.leaf ⟨(25, 13899936104448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00010.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12881 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 12881 12981 :=
  block_of_table results 12881 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0300
