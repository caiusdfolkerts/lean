module
prelude
import GraphInputsRow24Part00084Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0200
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24520071348224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24521111404544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record001_result⟩)
 (.leaf ⟨(24, 24521243361920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 24567299211520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 24567307307136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record004_result⟩)
 (.leaf ⟨(24, 24567769729152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 24569503156352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 24569651986432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record007_result⟩)
 (.leaf ⟨(24, 24571583531136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 24576089145600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 24576091291648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record010_result⟩)
 (.leaf ⟨(24, 24576138690816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10653 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 10653 10665 :=
  block_of_table results 10653 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0200
