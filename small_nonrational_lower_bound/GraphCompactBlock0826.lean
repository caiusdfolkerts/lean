module
prelude
import GraphInputsRow31Part00038Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0826
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 7606387277824), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 7606932340736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038.record001_result⟩)
 (.leaf ⟨(31, 7615253839872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 7623567081472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 7624103821312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038.record004_result⟩)
 (.leaf ⟨(31, 7736985190400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25797 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 25797 25803 :=
  block_of_table results 25797 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0826
