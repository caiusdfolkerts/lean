module
prelude
import GraphInputsRow24Part00171Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0287
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 34675150029312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_result⟩)
 (.leaf ⟨(24, 34675150553088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 34681861050624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 34681895059456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record003_result⟩)
 (.leaf ⟨(24, 34682976600064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 34683505082368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record005_result⟩)
 (.leaf ⟨(24, 34699074863104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 34703629619200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 34712462690320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record008_result⟩)
 (.leaf ⟨(24, 34712479334928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12101 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 12101 12111 :=
  block_of_table results 12101 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0287
