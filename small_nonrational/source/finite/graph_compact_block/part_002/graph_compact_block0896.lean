module
prelude
import GraphInputsRow31Part00108Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0896
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 24778740236544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record000_result⟩)
 (.leaf ⟨(31, 24779545379328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 24792300257280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 24826592886784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record003_result⟩)
 (.leaf ⟨(31, 24867860644356), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 24868137467904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record005_result⟩)
 (.leaf ⟨(31, 24868665950208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 24936722726912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 25020369797120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record008_result⟩)
 (.leaf ⟨(31, 25032348663808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00108.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26397 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 26397 26407 :=
  block_of_table results 26397 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0896
