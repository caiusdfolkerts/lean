module
prelude
import GraphInputsRow31Part00060Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0848
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 12714449633536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record000_result⟩)
 (.leaf ⟨(31, 12721978933248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 12723043762176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record002_result⟩)
 (.leaf ⟨(31, 12723580567552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 12731629502464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record004_result⟩)
 (.leaf ⟨(31, 12732166307840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 12738910814208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 12739678830592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record007_result⟩)
 (.leaf ⟨(31, 12786403442688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25952 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 25952 25961 :=
  block_of_table results 25952 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0848
