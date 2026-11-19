module
prelude
import GraphInputsRow31Part00101Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0889
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 22319602860608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 22545928585472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101.record001_result⟩)
 (.leaf ⟨(31, 22627569696768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 22669651083264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101.record003_result⟩)
 (.leaf ⟨(31, 22734075592704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 22737699536896), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101.record005_result⟩)
 (.leaf ⟨(31, 22862924611584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26345 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26345 26352 :=
  block_of_table results 26345 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0889
