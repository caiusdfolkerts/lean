module
prelude
import GraphInputsRow29Part00121Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0555
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 20724022804480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record000_result⟩)
 (.leaf ⟨(29, 20727531077888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 20727807868928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 20727915151360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record003_result⟩)
 (.leaf ⟨(29, 20728067948544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 20728072110080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 20728183554048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_result⟩)
 (.leaf ⟨(29, 20731807301888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 20732612444672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 20736121012352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record009_result⟩)
 (.leaf ⟨(29, 20736505053184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22247 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 22247 22258 :=
  block_of_table results 22247 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0555
