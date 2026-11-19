module
prelude
import GraphInputsRow23Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0108
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 32782688452608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record000_result⟩)
 (.leaf ⟨(23, 32783216934912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 32788929576960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record002_result⟩)
 (.leaf ⟨(23, 32789458059264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 32804960346112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record004_result⟩)
 (.leaf ⟨(23, 32804994809856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 32806101057536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 32813571178496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record007_result⟩)
 (.leaf ⟨(23, 32822165241856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7660 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 7660 7669 :=
  block_of_table results 7660 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0108
