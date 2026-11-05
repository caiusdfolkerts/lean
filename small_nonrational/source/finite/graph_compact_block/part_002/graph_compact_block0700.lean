module
prelude
import GraphInputsRow29Part00266Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0700
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 33099576508416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 33133122552352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record001_result⟩)
 (.leaf ⟨(29, 33167417278464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 33204460388352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_result⟩)
 (.leaf ⟨(29, 33238827401216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 33260382195744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record005_result⟩)
 (.leaf ⟨(29, 33262458650752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23437 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23437 23444 :=
  block_of_table results 23437 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0700
