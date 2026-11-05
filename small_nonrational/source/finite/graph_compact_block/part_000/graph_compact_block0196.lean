module
prelude
import GraphInputsRow24Part00080Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0196
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24432324444416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24432477241600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record001_result⟩)
 (.leaf ⟨(24, 24432481468416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 24432487710720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record003_result⟩)
 (.leaf ⟨(24, 24432592847104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 24432605136896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_result⟩)
 (.leaf ⟨(24, 24432727048448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 24436891779072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 24437021737728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record008_result⟩)
 (.leaf ⟨(24, 24438565568768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 24438918627584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record010_result⟩)
 (.leaf ⟨(24, 24438920773632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 24438927015936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_result⟩)
 (.leaf ⟨(24, 24438968172800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10606 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 10606 10620 :=
  block_of_table results 10606 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0196
