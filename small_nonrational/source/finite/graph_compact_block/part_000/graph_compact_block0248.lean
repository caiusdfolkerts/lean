module
prelude
import GraphInputsRow24Part00132Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0248
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 31530772594688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record000_result⟩)
 (.leaf ⟨(24, 31531235016704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 31537979523072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record002_result⟩)
 (.leaf ⟨(24, 31538053906432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 31538516328448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record004_result⟩)
 (.leaf ⟨(24, 31545532416256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 31545805045760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 31546069286912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record007_result⟩)
 (.leaf ⟨(24, 31546077609984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00132.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11676 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 11676 11685 :=
  block_of_table results 11676 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0248
