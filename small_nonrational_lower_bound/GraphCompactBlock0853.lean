module
prelude
import GraphInputsRow31Part00065Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0853
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 13234685878272), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 13238509043712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065.record001_result⟩)
 (.leaf ⟨(31, 13238769058048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 13238773284864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065.record003_result⟩)
 (.leaf ⟨(31, 13238835118336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 13238846627840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065.record005_result⟩)
 (.leaf ⟨(31, 13272859345152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25989 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 25989 25996 :=
  block_of_table results 25989 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0853
