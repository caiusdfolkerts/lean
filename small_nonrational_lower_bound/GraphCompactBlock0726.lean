module
prelude
import GraphInputsRow29Part00292Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0726
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 34763498848256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34789235230736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record001_result⟩)
 (.leaf ⟨(29, 34790308839940), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 34840774838528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 34875159609344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record004_result⟩)
 (.leaf ⟨(29, 34892331089920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23544 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23544 23550 :=
  block_of_table results 23544 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0726
