module
prelude
import GraphInputsRow24Part00120Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0236
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 28644513693824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_result⟩)
 (.leaf ⟨(24, 28666026279168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 28666094428416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record002_result⟩)
 (.leaf ⟨(24, 28701527965696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 28716202737792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record004_result⟩)
 (.leaf ⟨(24, 28717292339328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 28717294452736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record006_result⟩)
 (.leaf ⟨(24, 28717298484224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 28717426410112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record008_result⟩)
 (.leaf ⟨(24, 28727048691840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 28764811624448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record010_result⟩)
 (.leaf ⟨(24, 28769168408832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 28773397364736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record012_result⟩)
 (.leaf ⟨(24, 28781718962176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 28781850919552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 28794627833984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record015_result⟩)
 (.leaf ⟨(24, 28796163473536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11397 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 11397 11414 :=
  block_of_table results 11397 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0236
