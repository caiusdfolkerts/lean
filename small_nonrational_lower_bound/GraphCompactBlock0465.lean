module
prelude
import GraphInputsRow29Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0465
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 6995161677824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031.record000_result⟩)
 (.leaf ⟨(29, 6999458709504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7003082653696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 7003355217920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031.record003_result⟩)
 (.leaf ⟨(29, 7003619459072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20947 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 20947 20952 :=
  block_of_table results 20947 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0465
