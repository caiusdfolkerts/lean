module
prelude
import GraphInputsRow24Part00114Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0230
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27798256255232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record000_result⟩)
 (.leaf ⟨(24, 27798313896064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27799354083456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 27800658575360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record003_result⟩)
 (.leaf ⟨(24, 27801533548672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 27802738950144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record005_result⟩)
 (.leaf ⟨(24, 27807029674240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 27811324690432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 27811333013504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record008_result⟩)
 (.leaf ⟨(24, 27814379128960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11258 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 11258 11268 :=
  block_of_table results 11258 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0230
