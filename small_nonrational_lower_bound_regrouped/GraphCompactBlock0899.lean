module
prelude
import GraphInputsRow31Part00111Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0899
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 25611561074688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record000_result⟩)
 (.leaf ⟨(31, 25623911202816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 25634650783744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record002_result⟩)
 (.leaf ⟨(31, 25658203832320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 25703368163328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record004_result⟩)
 (.leaf ⟨(31, 25739881611264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 25757053091840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record006_result⟩)
 (.leaf ⟨(31, 25772093865984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00111.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26429 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26429 26437 :=
  block_of_table results 26429 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0899
