module
prelude
import GraphInputsRow29Part00147Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0581
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24511781012224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record000_result⟩)
 (.leaf ⟨(29, 24512183665216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24512184729600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record002_result⟩)
 (.leaf ⟨(29, 24518229753856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 24521247555584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record004_result⟩)
 (.leaf ⟨(29, 24569515671552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 24570031800320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record006_result⟩)
 (.leaf ⟨(29, 24572112175104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22588 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 22588 22596 :=
  block_of_table results 22588 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0581
