module
prelude
import GraphInputsRow31Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0821
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 7206990807296), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 7275674763520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033.record001_result⟩)
 (.leaf ⟨(31, 7276479906304), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 7276488294400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 7291512881152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033.record004_result⟩)
 (.leaf ⟨(31, 7294542675968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25758 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 25758 25764 :=
  block_of_table results 25758 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0821
