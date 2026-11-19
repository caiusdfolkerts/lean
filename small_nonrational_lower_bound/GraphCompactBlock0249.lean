module
prelude
import GraphInputsRow24Part00133Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0249
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 31546267467776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31551971721472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record001_result⟩)
 (.leaf ⟨(24, 31552508592128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31552516915200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record003_result⟩)
 (.leaf ⟨(24, 31553011908864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31560561623296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record005_result⟩)
 (.leaf ⟨(24, 31560830091264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 31560838414336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 31561299795968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record008_result⟩)
 (.leaf ⟨(24, 31561601810688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 31562373013504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record010_result⟩)
 (.leaf ⟨(24, 31568044237056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 31569151590400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record012_result⟩)
 (.leaf ⟨(24, 31569688395776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11685 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 11685 11699 :=
  block_of_table results 11685 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0249
