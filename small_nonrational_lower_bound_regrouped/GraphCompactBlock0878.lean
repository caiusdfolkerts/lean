module
prelude
import GraphInputsRow31Part00090Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0878
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 17748224647232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 17775403728897), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record001_result⟩)
 (.leaf ⟨(31, 17775403794432), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 17777484169216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 17783725228033), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record004_result⟩)
 (.leaf ⟨(31, 17783993696256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26242 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26242 26248 :=
  block_of_table results 26242 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0878
