module
prelude
import GraphInputsRow31Part00073Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0861
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 13900393218592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 13900394332160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073.record001_result⟩)
 (.leaf ⟨(31, 13933431816192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 13933440139264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073.record003_result⟩)
 (.leaf ⟨(31, 13941740732416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 13942277537792), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073.record005_result⟩)
 (.leaf ⟨(31, 14027648934144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26050 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26050 26057 :=
  block_of_table results 26050 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0861
