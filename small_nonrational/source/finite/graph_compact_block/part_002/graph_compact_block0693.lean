module
prelude
import GraphInputsRow29Part00259Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0693
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 32779208261888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00259.record000_result⟩)
 (.leaf ⟨(29, 32782688452608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00259.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32783216934912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00259.record002_result⟩)
 (.leaf ⟨(29, 32788929576960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00259.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23410 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23410 23414 :=
  block_of_table results 23410 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0693
