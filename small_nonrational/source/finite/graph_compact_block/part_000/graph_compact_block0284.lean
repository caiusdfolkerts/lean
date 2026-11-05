module
prelude
import GraphInputsRow24Part00168Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0284
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 34497227923520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 34497228980224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_result⟩)
 (.leaf ⟨(24, 34497230800896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 34497278249024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 34498318305344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_result⟩)
 (.leaf ⟨(24, 34498320402432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 34498334949952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 34498452390408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_result⟩)
 (.leaf ⟨(24, 34635841569024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 34635845795840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 34635853598720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_result⟩)
 (.leaf ⟨(24, 34637873185024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12072 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 12072 12084 :=
  block_of_table results 12072 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0284
