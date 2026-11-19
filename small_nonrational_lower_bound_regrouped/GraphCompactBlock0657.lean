module
prelude
import GraphInputsRow29Part00223Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0657
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 30242743779856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 30246537592832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record001_result⟩)
 (.leaf ⟨(29, 30246636683264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 30253917671552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record003_result⟩)
 (.leaf ⟨(29, 30254152552464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 30255226028560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_result⟩)
 (.leaf ⟨(29, 30305583108096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23159 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23159 23166 :=
  block_of_table results 23159 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0657
