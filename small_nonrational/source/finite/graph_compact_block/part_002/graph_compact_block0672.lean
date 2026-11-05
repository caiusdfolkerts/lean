module
prelude
import GraphInputsRow29Part00238Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0672
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 31510166044928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record000_result⟩)
 (.leaf ⟨(29, 31519296978944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 31520840548352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record002_result⟩)
 (.leaf ⟨(29, 31527345913856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 31527618478080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record004_result⟩)
 (.leaf ⟨(29, 31529426288640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 31530160226816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record006_result⟩)
 (.leaf ⟨(29, 31530161274880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00238.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23313 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 23313 23321 :=
  block_of_table results 23313 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0672
