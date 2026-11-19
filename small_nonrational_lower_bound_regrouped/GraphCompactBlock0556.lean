module
prelude
import GraphInputsRow29Part00122Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0556
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 20740397236352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record000_result⟩)
 (.leaf ⟨(29, 20744692187264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 20748987170816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record002_result⟩)
 (.leaf ⟨(29, 20749255573504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 20758856269824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record004_result⟩)
 (.leaf ⟨(29, 20792091934720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 20792608063488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record006_result⟩)
 (.leaf ⟨(29, 20800937656320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22258 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 22258 22266 :=
  block_of_table results 22258 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0556
