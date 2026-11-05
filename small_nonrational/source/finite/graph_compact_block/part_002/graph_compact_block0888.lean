module
prelude
import GraphInputsRow31Part00100Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0888
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 22043462483968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 22064925802752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100.record001_result⟩)
 (.leaf ⟨(31, 22077408051456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 22146538553344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 22179774218240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100.record004_result⟩)
 (.leaf ⟨(31, 22182166069248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26339 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26339 26345 :=
  block_of_table results 26339 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0888
