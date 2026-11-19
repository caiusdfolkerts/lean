module
prelude
import GraphInputsRow19Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0052
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(19, 17189021704192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record000_result⟩)
 (.leaf ⟨(19, 17189073586192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record001_result⟩))
 (.branch 3
 (.leaf ⟨(19, 17190106497024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record002_result⟩)
 (.leaf ⟨(19, 17192393375744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(19, 17195480907776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record004_result⟩)
 (.leaf ⟨(19, 17198336708608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record005_result⟩))
 (.branch 7
 (.leaf ⟨(19, 17198468825089), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record006_result⟩)
 (.leaf ⟨(19, 17198468829184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(19, 17200305963264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record008_result⟩)
 (.leaf ⟨(19, 17200442310656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record009_result⟩))
 (.branch 11
 (.leaf ⟨(19, 17200450633728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record010_result⟩)
 (.leaf ⟨(19, 17200582754304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(19, 17200673521664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record012_result⟩)
 (.leaf ⟨(19, 17201210327040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record013_result⟩))
 (.branch 15
 (.leaf ⟨(19, 17203802406912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record014_result⟩)
 (.branch 16
 (.leaf ⟨(19, 17207451451392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record015_result⟩)
 (.leaf ⟨(19, 17215457919232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(19, 17215466307584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record017_result⟩)
 (.leaf ⟨(19, 17215598428160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record018_result⟩))
 (.branch 20
 (.leaf ⟨(19, 17215705645312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record019_result⟩)
 (.leaf ⟨(19, 17215858442496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 17215862669312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record021_result⟩)
 (.leaf ⟨(19, 17215974048000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 17215986337792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record023_result⟩)
 (.leaf ⟨(19, 17218809692416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(19, 17218818080768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record025_result⟩)
 (.leaf ⟨(19, 17219082321920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record026_result⟩))
 (.branch 28
 (.leaf ⟨(19, 17219090124800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record027_result⟩)
 (.leaf ⟨(19, 17219094610176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(19, 17219106899968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record029_result⟩)
 (.leaf ⟨(19, 17219329462528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record030_result⟩))
 (.branch 32
 (.leaf ⟨(19, 17222986957056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 17223375192064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record032_result⟩)
 (.leaf ⟨(19, 17223382994944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record033_result⟩)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ⟨(19, 17223399770112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record034_result⟩)
 (.leaf ⟨(19, 17223490212096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record035_result⟩))
 (.branch 37
 (.leaf ⟨(19, 17227131191552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record036_result⟩)
 (.leaf ⟨(19, 17227668062208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(19, 17227676385280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record038_result⟩)
 (.leaf ⟨(19, 17228724633600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record039_result⟩))
 (.branch 41
 (.leaf ⟨(19, 17228732956672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record040_result⟩)
 (.leaf ⟨(19, 17231589148672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record041_result⟩))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ⟨(19, 17231721269248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record042_result⟩)
 (.leaf ⟨(19, 17231968735232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record043_result⟩))
 (.branch 45
 (.leaf ⟨(19, 17231985510400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record044_result⟩)
 (.leaf ⟨(19, 17232885187328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 17235721093376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record046_result⟩)
 (.leaf ⟨(19, 17235758350336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 17235766673408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record048_result⟩)
 (.branch 50
 (.leaf ⟨(19, 17235989561344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record049_result⟩)
 (.leaf ⟨(19, 17235997884416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record050_result⟩))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(19, 17236509065744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record051_result⟩)
 (.leaf ⟨(19, 17236509331456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record052_result⟩))
 (.branch 54
 (.leaf ⟨(19, 17236526366720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record053_result⟩)
 (.leaf ⟨(19, 17236777664768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(19, 17237046132736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record055_result⟩)
 (.leaf ⟨(19, 17237054455808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record056_result⟩))
 (.branch 58
 (.leaf ⟨(19, 17237582807552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record057_result⟩)
 (.branch 59
 (.leaf ⟨(19, 17244293828864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record058_result⟩)
 (.leaf ⟨(19, 17244327444480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record059_result⟩)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf ⟨(19, 17244335767552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record060_result⟩)
 (.leaf ⟨(19, 17244830699520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record061_result⟩))
 (.branch 63
 (.leaf ⟨(19, 17244864119296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record062_result⟩)
 (.leaf ⟨(19, 17283233939712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record063_result⟩)))
 (.branch 66
 (.branch 65
 (.leaf ⟨(19, 17283242328064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record064_result⟩)
 (.leaf ⟨(19, 17283502342400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record065_result⟩))
 (.branch 67
 (.leaf ⟨(19, 17283514632192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record066_result⟩)
 (.branch 68
 (.leaf ⟨(19, 17283753969920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record067_result⟩)
 (.leaf ⟨(19, 17292091982592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00012.record068_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3296 + i))) 0 69 :=
  interval_of_check _ 0 69 (by decide +kernel)

public theorem complete : Block 3296 3365 :=
  block_of_table results 3296 69 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0052
