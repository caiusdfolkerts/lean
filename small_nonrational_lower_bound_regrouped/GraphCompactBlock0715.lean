module
prelude
import GraphInputsRow29Part00281Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0715
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 34239680876544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34240553164864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record001_result⟩)
 (.leaf ⟨(29, 34240754352640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 34241626902592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 34278133989892), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record004_result⟩)
 (.leaf ⟨(29, 34497194631232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23493 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23493 23499 :=
  block_of_table results 23493 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0715
