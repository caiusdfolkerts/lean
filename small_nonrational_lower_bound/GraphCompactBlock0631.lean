module
prelude
import GraphInputsRow29Part00197Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0631
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 28627837141120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 28628519751680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197.record001_result⟩)
 (.leaf ⟨(29, 28628776157312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 28628910358656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197.record003_result⟩)
 (.leaf ⟨(29, 28631537582080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 28640119128192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197.record005_result⟩)
 (.leaf ⟨(29, 28640123322368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22982 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 22982 22989 :=
  block_of_table results 22982 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0631
