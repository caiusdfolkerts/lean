module
prelude
import GraphInputsRow24Part00088Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0204
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24645193703488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24647340917312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record001_result⟩)
 (.leaf ⟨(24, 24663849844800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 24663984062464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 24663986143232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record004_result⟩)
 (.leaf ⟨(24, 24665997320256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 24666064437248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 24666066518016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_result⟩)
 (.leaf ⟨(24, 24666198508032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 24672536117248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record009_result⟩)
 (.leaf ⟨(24, 24672734298112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 24672775454976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record011_result⟩)
 (.leaf ⟨(24, 24676940185600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10725 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 10725 10738 :=
  block_of_table results 10725 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0204
