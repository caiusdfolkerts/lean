module
prelude
import GraphInputsRow24Part00136Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0252
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 31605053849600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record000_result⟩)
 (.leaf ⟨(24, 31622042750976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 31622099902720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record002_result⟩)
 (.leaf ⟨(24, 31655386480640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 31659621613568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record004_result⟩)
 (.leaf ⟨(24, 31689679110144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 31722914775040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 31722964320256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record007_result⟩)
 (.leaf ⟨(24, 31751688716544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11720 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 11720 11729 :=
  block_of_table results 11720 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0252
