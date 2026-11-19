module
prelude
import GraphInputsRow31Part00127Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0915
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 28830106451968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record000_result⟩)
 (.leaf ⟨(31, 28834539765760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 28835068248064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record002_result⟩)
 (.leaf ⟨(31, 28847286255616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 28871055908928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record004_result⟩)
 (.leaf ⟨(31, 28875099750528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 28875468316672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 28898823798912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record007_result⟩)
 (.leaf ⟨(31, 28967545372672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26532 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 26532 26541 :=
  block_of_table results 26532 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0915
