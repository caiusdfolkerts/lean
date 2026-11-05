module
prelude
import GraphInputsRow24Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0136
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 11960825413633), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 11965885843712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record001_result⟩)
 (.leaf ⟨(24, 11966334124160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 11966334156800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 11974475778176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record004_result⟩)
 (.leaf ⟨(24, 11983010152576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 11983012265984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 11983045296128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record007_result⟩)
 (.leaf ⟨(24, 11984101867520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 11984105899008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 11991704240128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record010_result⟩)
 (.leaf ⟨(24, 11991842603008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 12000277235712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 12021617787904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record013_result⟩)
 (.leaf ⟨(24, 12098023293184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 12098425897216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 12100301848832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record016_result⟩)
 (.leaf ⟨(24, 12104865202432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 12113089232912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 12113455136896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record019_result⟩)
 (.leaf ⟨(24, 12133454938368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 12133842649104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record021_result⟩)
 (.leaf ⟨(24, 12133845221504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 12142287786240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record023_result⟩)
 (.leaf ⟨(24, 12165654872192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(24, 12165658542096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record025_result⟩)
 (.branch 27
 (.leaf ⟨(24, 12165789040896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record026_result⟩)
 (.leaf ⟨(24, 12166054903824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(24, 12172494209040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record028_result⟩)
 (.branch 30
 (.leaf ⟨(24, 12172499902592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record029_result⟩)
 (.leaf ⟨(24, 12174500040960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(24, 12211007324160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 12234374299904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record032_result⟩)
 (.leaf ⟨(24, 12236655976704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(24, 12236918718480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record034_result⟩)
 (.branch 36
 (.leaf ⟨(24, 12255186927744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_result⟩)
 (.leaf ⟨(24, 12327967588352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(24, 12371810680848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record037_result⟩)
 (.branch 39
 (.leaf ⟨(24, 12372213284880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record038_result⟩)
 (.leaf ⟨(24, 12374089236496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(24, 12378652590096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record040_result⟩)
 (.branch 42
 (.leaf ⟨(24, 12384035946624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_result⟩)
 (.leaf ⟨(24, 12392357445760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(24, 12439512942720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record043_result⟩)
 (.branch 45
 (.leaf ⟨(24, 12439587422464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record044_result⟩)
 (.leaf ⟨(24, 12439587487744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(24, 12439855857792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record046_result⟩)
 (.leaf ⟨(24, 12439857971200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record047_result⟩))
 (.branch 49
 (.leaf ⟨(24, 12464046489728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record048_result⟩)
 (.leaf ⟨(24, 12465136091264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8804 + i))) 0 50 :=
  interval_of_check _ 0 50 (by decide +kernel)

public theorem complete : Block 8804 8854 :=
  block_of_table results 8804 50 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0136
