module
prelude
import GraphInputsRow31Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0808
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 5104178569216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 5107521954048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020.record001_result⟩)
 (.leaf ⟨(31, 5137340891136), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 5139066847488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020.record003_result⟩)
 (.leaf ⟨(31, 5141881160448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 5236370972928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020.record005_result⟩)
 (.leaf ⟨(31, 5241337577728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25659 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 25659 25666 :=
  block_of_table results 25659 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0808
