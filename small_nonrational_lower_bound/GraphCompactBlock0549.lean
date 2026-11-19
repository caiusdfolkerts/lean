module
prelude
import GraphInputsRow29Part00115Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0549
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 19718337462272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00115.record000_result⟩)
 (.leaf ⟨(29, 19718865944576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00115.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 19724775784704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00115.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 19729209163776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00115.record003_result⟩)
 (.leaf ⟨(29, 19729745969152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00115.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22169 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22169 22174 :=
  block_of_table results 22169 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0549
