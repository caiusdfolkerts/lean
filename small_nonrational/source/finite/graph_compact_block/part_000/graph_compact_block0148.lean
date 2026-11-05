module
prelude
import GraphInputsRow24Part00032Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0148
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 16712867053568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 16713403858944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record001_result⟩)
 (.leaf ⟨(24, 16717155696896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 16717490225152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 16721452793856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record004_result⟩)
 (.leaf ⟨(24, 16721725358080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 16722187780096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 16729469091840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record007_result⟩)
 (.leaf ⟨(24, 16735478546688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 16739911925760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 16740448731136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record010_result⟩)
 (.leaf ⟨(24, 16744609480704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9263 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 9263 9275 :=
  block_of_table results 9263 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0148
