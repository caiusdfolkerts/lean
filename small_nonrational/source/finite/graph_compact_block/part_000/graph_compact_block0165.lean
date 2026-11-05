module
prelude
import GraphInputsRow24Part00049Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0165
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 19595331125248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 19595520917760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record001_result⟩)
 (.leaf ⟨(24, 19596360843520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 19596365070336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 19602341890176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record004_result⟩)
 (.leaf ⟨(24, 19611626512448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 19611963654400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 19612100001792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record007_result⟩)
 (.leaf ⟨(24, 19612108324864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 19612232122368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record009_result⟩)
 (.leaf ⟨(24, 19612240445440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 19612504686592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record011_result⟩)
 (.leaf ⟨(24, 19612700786688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00049.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9726 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 9726 9739 :=
  block_of_table results 9726 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0165
