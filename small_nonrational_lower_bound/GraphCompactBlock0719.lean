module
prelude
import GraphInputsRow29Part00285Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0719
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 34636227020816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00285.record000_result⟩)
 (.leaf ⟨(29, 34636243665424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00285.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 34636495589376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00285.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 34640022798336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00285.record003_result⟩)
 (.leaf ⟨(29, 34640295362560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00285.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23518 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23518 23523 :=
  block_of_table results 23518 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0719
