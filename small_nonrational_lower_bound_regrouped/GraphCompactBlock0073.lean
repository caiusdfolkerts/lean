module
prelude
import GraphInputsRow19Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0073
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 31977218514944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 31977408307456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record001_result⟩)
 (.leaf ⟨(19, 31977416695808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 31977441337600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 31977680936960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record004_result⟩)
 (.leaf ⟨(19, 31977911099424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 31977979248640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 31978489913344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record007_result⟩)
 (.leaf ⟨(19, 31990146466048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 31990150627584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 31990150692864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record010_result⟩)
 (.leaf ⟨(19, 31990153748736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 31990547054592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 31993522817280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record013_result⟩)
 (.leaf ⟨(19, 31993769828352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 31993794398240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 32010442670336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record016_result⟩)
 (.leaf ⟨(19, 32010446897152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 32010454179840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 32010685390848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record019_result⟩)
 (.leaf ⟨(19, 32010949632000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(19, 32011532271872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record021_result⟩)
 (.branch 23
 (.leaf ⟨(19, 32011536498688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record022_result⟩)
 (.leaf ⟨(19, 32011544691712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(19, 32011733573888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record024_result⟩)
 (.branch 26
 (.leaf ⟨(19, 32011741962240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record025_result⟩)
 (.leaf ⟨(19, 32011742872576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(19, 32011800544000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record027_result⟩)
 (.branch 29
 (.leaf ⟨(19, 32012270305824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record028_result⟩)
 (.leaf ⟨(19, 32012337414656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(19, 32024442773568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record030_result⟩)
 (.branch 32
 (.leaf ⟨(19, 32024905195584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record031_result⟩)
 (.leaf ⟨(19, 32041615245568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(19, 32042152116224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record033_result⟩)
 (.branch 35
 (.leaf ⟨(19, 32044215698496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record034_result⟩)
 (.leaf ⟨(19, 32076510265920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(19, 32076512363008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record036_result⟩)
 (.branch 38
 (.leaf ⟨(19, 32078039286784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record037_result⟩)
 (.leaf ⟨(19, 32162075713600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(19, 32164760010752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record039_result⟩)
 (.branch 41
 (.leaf ⟨(19, 32169860280384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record040_result⟩)
 (.leaf ⟨(19, 32171001135104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(19, 32172569265216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record042_result⟩)
 (.branch 44
 (.leaf ⟨(19, 32173064717376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record043_result⟩)
 (.leaf ⟨(19, 32196220094528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(19, 32196236739136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record045_result⟩)
 (.leaf ⟨(19, 32220879520832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record046_result⟩))
 (.branch 48
 (.leaf ⟨(19, 32230595461120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record047_result⟩)
 (.leaf ⟨(19, 32230664577280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record048_result⟩)))))))
 (.branch 74
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf ⟨(19, 32230664642560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record049_result⟩)
 (.branch 51
 (.leaf ⟨(19, 32230671917088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record050_result⟩)
 (.leaf ⟨(19, 32230722242592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record051_result⟩)))
 (.branch 53
 (.leaf ⟨(19, 32231734673664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record052_result⟩)
 (.branch 54
 (.leaf ⟨(19, 32231734738944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record053_result⟩)
 (.leaf ⟨(19, 32231737794816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record054_result⟩))))
 (.branch 58
 (.branch 56
 (.leaf ⟨(19, 32231737860096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record055_result⟩)
 (.branch 57
 (.leaf ⟨(19, 32231742021632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record056_result⟩)
 (.leaf ⟨(19, 32231745654816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record057_result⟩)))
 (.branch 59
 (.leaf ⟨(19, 32232869724161), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record058_result⟩)
 (.branch 60
 (.leaf ⟨(19, 32233835464960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record059_result⟩)
 (.leaf ⟨(19, 32233842804768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record060_result⟩)))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf ⟨(19, 32234040985632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record061_result⟩)
 (.branch 63
 (.leaf ⟨(19, 32236699656192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record062_result⟩)
 (.leaf ⟨(19, 32236700696576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record063_result⟩)))
 (.branch 65
 (.leaf ⟨(19, 32263880671232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record064_result⟩)
 (.branch 66
 (.leaf ⟨(19, 32263950567680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record065_result⟩)
 (.leaf ⟨(19, 32263957907488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record066_result⟩))))
 (.branch 70
 (.branch 68
 (.leaf ⟨(19, 32264008239112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record067_result⟩)
 (.branch 69
 (.leaf ⟨(19, 32266088612872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record068_result⟩)
 (.leaf ⟨(19, 32266105389057), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record069_result⟩)))
 (.branch 72
 (.branch 71
 (.leaf ⟨(19, 32268160731392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record070_result⟩)
 (.leaf ⟨(19, 32268366252064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record071_result⟩))
 (.branch 73
 (.leaf ⟨(19, 32437896286464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record072_result⟩)
 (.leaf ⟨(19, 32438296809728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record073_result⟩))))))
 (.branch 86
 (.branch 80
 (.branch 77
 (.branch 75
 (.leaf ⟨(19, 32438952857856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record074_result⟩)
 (.branch 76
 (.leaf ⟨(19, 32440182181920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record075_result⟩)
 (.leaf ⟨(19, 32440182186000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record076_result⟩)))
 (.branch 78
 (.leaf ⟨(19, 32440446423072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record077_result⟩)
 (.branch 79
 (.leaf ⟨(19, 32440446427152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record078_result⟩)
 (.leaf ⟨(19, 32441272639744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record079_result⟩))))
 (.branch 83
 (.branch 81
 (.leaf ⟨(19, 32450131009536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record080_result⟩)
 (.branch 82
 (.leaf ⟨(19, 32458452508672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record081_result⟩)
 (.leaf ⟨(19, 32473746538752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record082_result⟩)))
 (.branch 84
 (.leaf ⟨(19, 32474524747792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record083_result⟩)
 (.branch 85
 (.leaf ⟨(19, 32490389537024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record084_result⟩)
 (.leaf ⟨(19, 32490525884416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record085_result⟩)))))
 (.branch 92
 (.branch 89
 (.branch 87
 (.leaf ⟨(19, 32490534207488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record086_result⟩)
 (.branch 88
 (.leaf ⟨(19, 32490757095424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record087_result⟩)
 (.leaf ⟨(19, 32490930569216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record088_result⟩)))
 (.branch 90
 (.leaf ⟨(19, 32504606433296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record089_result⟩)
 (.branch 91
 (.leaf ⟨(19, 32505680371968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record090_result⟩)
 (.leaf ⟨(19, 32505944613120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record091_result⟩))))
 (.branch 95
 (.branch 93
 (.leaf ⟨(19, 32505969248288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record092_result⟩)
 (.branch 94
 (.leaf ⟨(19, 32506737002512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record093_result⟩)
 (.leaf ⟨(19, 32513481771040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record094_result⟩)))
 (.branch 97
 (.branch 96
 (.leaf ⟨(19, 32514538741760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record095_result⟩)
 (.leaf ⟨(19, 32514564489216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record096_result⟩))
 (.branch 98
 (.leaf ⟨(19, 32514572812288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record097_result⟩)
 (.leaf ⟨(19, 32521803270176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record098_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5282 + i))) 0 99 :=
  interval_of_check _ 0 99 (by decide +kernel)

public theorem complete : Block 5282 5381 :=
  block_of_table results 5282 99 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0073
