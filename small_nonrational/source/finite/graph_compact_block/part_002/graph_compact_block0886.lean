module
prelude
import GraphInputsRow31Part00098Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0886
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 21514565091584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 21528125112320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098.record001_result⟩)
 (.leaf ⟨(31, 21530708869120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 21660065333248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098.record003_result⟩)
 (.leaf ⟨(31, 21668386832384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 21668915314688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098.record005_result⟩)
 (.leaf ⟨(31, 21672547581952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26324 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26324 26331 :=
  block_of_table results 26324 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0886
