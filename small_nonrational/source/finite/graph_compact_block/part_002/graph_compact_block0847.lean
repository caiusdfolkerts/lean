module
prelude
import GraphInputsRow31Part00059Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0847
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 12577950203904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 12582383517696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059.record001_result⟩)
 (.leaf ⟨(31, 12582912000000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 12587072749568), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 12595130007552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059.record004_result⟩)
 (.leaf ⟨(31, 12654450638848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25946 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 25946 25952 :=
  block_of_table results 25946 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0847
