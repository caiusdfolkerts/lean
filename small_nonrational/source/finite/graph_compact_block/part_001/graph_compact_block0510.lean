module
prelude
import GraphInputsRow29Part00076Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0510
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 12586812702720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00076.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 12587072750080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00076.record001_result⟩)
 (.leaf ⟨(29, 12592861954176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00076.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 12593045733376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00076.record003_result⟩)
 (.leaf ⟨(29, 12594991743104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00076.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 12645748969728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00076.record005_result⟩)
 (.leaf ⟨(29, 12648968622336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00076.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21513 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 21513 21520 :=
  block_of_table results 21513 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0510
