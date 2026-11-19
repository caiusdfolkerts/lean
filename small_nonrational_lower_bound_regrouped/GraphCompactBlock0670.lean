module
prelude
import GraphInputsRow29Part00236Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0670
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 31431376510976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record000_result⟩)
 (.leaf ⟨(29, 31441580785920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 31448308449280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record002_result⟩)
 (.leaf ⟨(29, 31448316772352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 31450174914560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record004_result⟩)
 (.leaf ⟨(29, 31450711719936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 31465001779200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 31465736765440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record007_result⟩)
 (.leaf ⟨(29, 31474082648096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23293 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 23293 23302 :=
  block_of_table results 23293 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0670
