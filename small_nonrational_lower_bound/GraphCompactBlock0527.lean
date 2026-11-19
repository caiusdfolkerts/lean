module
prelude
import GraphInputsRow29Part00093Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0527
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 16531623247873), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_result⟩)
 (.leaf ⟨(29, 16531623313408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 16531883327744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 16531891716096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record003_result⟩)
 (.leaf ⟨(29, 16531895357440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 16532675559680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record005_result⟩)
 (.leaf ⟨(29, 16532948287488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 16533212430336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 16533220753408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record008_result⟩)
 (.leaf ⟨(29, 16536188227584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21806 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 21806 21816 :=
  block_of_table results 21806 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0527
