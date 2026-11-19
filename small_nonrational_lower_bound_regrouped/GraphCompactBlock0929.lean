module
prelude
import GraphInputsRow31Part00141Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0929
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 30249488809984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 30254859059200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141.record001_result⟩)
 (.leaf ⟨(31, 30255226552320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 30258078711808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 30305306575104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141.record004_result⟩)
 (.leaf ⟨(31, 30313896542208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26586 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26586 26592 :=
  block_of_table results 26586 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0929
