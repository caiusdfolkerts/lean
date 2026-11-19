module
prelude
import GraphInputsRow31Part00174Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0962
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 34635690149904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record000_result⟩)
 (.leaf ⟨(31, 34635707383808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 34635727831040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record002_result⟩)
 (.leaf ⟨(31, 34635740348928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 34635748737024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record004_result⟩)
 (.leaf ⟨(31, 34635828494336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 34636244189184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 34644321894400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record007_result⟩)
 (.leaf ⟨(31, 34644850376704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26783 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 26783 26792 :=
  block_of_table results 26783 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0962
