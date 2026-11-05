module
prelude
import GraphInputsRow29Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0450
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 3921599365120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record000_result⟩)
 (.leaf ⟨(29, 3921602941184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 3922123032592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 3922655871232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_result⟩)
 (.leaf ⟨(29, 3922655936512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20727 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 20727 20732 :=
  block_of_table results 20727 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0450
