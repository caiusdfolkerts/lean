module
prelude
import GraphInputsRow29Part00247Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0681
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 31995635761152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00247.record000_result⟩)
 (.leaf ⟨(29, 32010462625792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00247.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32028125307136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00247.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 32041010208832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00247.record003_result⟩)
 (.leaf ⟨(29, 32041127383072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00247.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23356 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23356 23361 :=
  block_of_table results 23356 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0681
