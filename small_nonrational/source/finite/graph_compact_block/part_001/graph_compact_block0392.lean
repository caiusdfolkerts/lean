module
prelude
import GraphInputsRow26Part00076Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0392
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 32780558794752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record000_result⟩)
 (.leaf ⟨(26, 32780600016896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 32781069721600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record002_result⟩)
 (.leaf ⟨(26, 32782411792640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 32783216935424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record004_result⟩)
 (.leaf ⟨(26, 32787797647616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 32787881328640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record006_result⟩)
 (.leaf ⟨(26, 32788334518272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17476 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 17476 17484 :=
  block_of_table results 17476 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0392
