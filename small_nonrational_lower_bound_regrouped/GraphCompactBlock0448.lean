module
prelude
import GraphInputsRow29Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0448
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 3629920583808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014.record000_result⟩)
 (.leaf ⟨(29, 3647842877440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 3784067809536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014.record002_result⟩)
 (.leaf ⟨(29, 3786689019904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20714 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 20714 20718 :=
  block_of_table results 20714 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0448
