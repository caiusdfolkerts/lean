module
prelude
import GraphInputsRow29Part00201Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0635
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 28899897540736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record000_result⟩)
 (.leaf ⟨(29, 28900165976064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28900170137600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record002_result⟩)
 (.leaf ⟨(29, 28901977915520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 28902114230272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record004_result⟩)
 (.leaf ⟨(29, 28902246350848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 28902250512384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record006_result⟩)
 (.leaf ⟨(29, 28909459488896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00201.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23014 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 23014 23022 :=
  block_of_table results 23014 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0635
