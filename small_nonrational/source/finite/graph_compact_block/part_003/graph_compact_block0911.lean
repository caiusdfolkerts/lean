module
prelude
import GraphInputsRow31Part00123Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0911
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 27266738323456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record000_result⟩)
 (.leaf ⟨(31, 27307402207360), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 27404177244160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record002_result⟩)
 (.leaf ⟨(31, 27562495442944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 27575435952128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record004_result⟩)
 (.leaf ⟨(31, 28041170976768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 28076487016448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record006_result⟩)
 (.leaf ⟨(31, 28076495339520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26502 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26502 26510 :=
  block_of_table results 26502 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0911
