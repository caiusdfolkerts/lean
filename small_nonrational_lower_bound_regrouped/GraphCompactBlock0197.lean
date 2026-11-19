module
prelude
import GraphInputsRow24Part00081Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0197
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24438978381824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24441182487296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record001_result⟩)
 (.leaf ⟨(24, 24443262862080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 24447155470592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record003_result⟩)
 (.leaf ⟨(24, 24447167760384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 24447289671936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record005_result⟩)
 (.leaf ⟨(24, 24447299880960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 24447365941248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 24447512756224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record008_result⟩)
 (.leaf ⟨(24, 24447759425600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 24449906639424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record010_result⟩)
 (.leaf ⟨(24, 24457691414784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 24457825681408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record012_result⟩)
 (.leaf ⟨(24, 24457834004480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10620 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 10620 10634 :=
  block_of_table results 10620 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0197
