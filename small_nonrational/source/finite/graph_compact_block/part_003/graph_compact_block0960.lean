module
prelude
import GraphInputsRow31Part00172Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0960
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 34145025654784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record000_result⟩)
 (.leaf ⟨(31, 34187960713216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 34213709611008), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record002_result⟩)
 (.leaf ⟨(31, 34223442427904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 34228783808512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record004_result⟩)
 (.leaf ⟨(31, 34240622231552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 34240754352128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record006_result⟩)
 (.leaf ⟨(31, 34241662418944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00172.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26762 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26762 26770 :=
  block_of_table results 26762 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0960
