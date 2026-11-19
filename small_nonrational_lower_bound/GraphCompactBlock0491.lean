module
prelude
import GraphInputsRow29Part00057Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0491
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 10859097098240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 10861037027584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057.record001_result⟩)
 (.leaf ⟨(29, 10876537044992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 10892192579584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 10892439980288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057.record004_result⟩)
 (.leaf ⟨(29, 10896600598784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21314 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 21314 21320 :=
  block_of_table results 21314 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0491
