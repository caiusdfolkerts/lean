module
prelude
import GraphInputsRow24Part00091Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0207
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24885603602496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24885654980624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_result⟩)
 (.leaf ⟨(24, 24886685745408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 24886728720385), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record003_result⟩)
 (.leaf ⟨(24, 24893844359184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 24894042540048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record005_result⟩)
 (.leaf ⟨(24, 24903865614336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 24950610133248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record007_result⟩)
 (.leaf ⟨(24, 24967790002176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 24968062566400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record009_result⟩)
 (.leaf ⟨(24, 24968524988416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 24986249134080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record011_result⟩)
 (.leaf ⟨(24, 25003428937728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 25003957420032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record013_result⟩)
 (.leaf ⟨(24, 25016328524032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10781 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 10781 10796 :=
  block_of_table results 10781 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0207
