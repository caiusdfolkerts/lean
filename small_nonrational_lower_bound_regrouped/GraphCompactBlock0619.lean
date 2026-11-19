module
prelude
import GraphInputsRow29Part00185Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0619
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 27080063000576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00185.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 27080335036448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00185.record001_result⟩)
 (.leaf ⟨(29, 27085483606016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00185.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 27094069346304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00185.record003_result⟩)
 (.leaf ⟨(29, 27110997557248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00185.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 27120709468416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00185.record005_result⟩)
 (.leaf ⟨(29, 27121378459648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00185.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22907 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 22907 22914 :=
  block_of_table results 22907 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0619
