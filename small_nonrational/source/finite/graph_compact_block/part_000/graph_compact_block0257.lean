module
prelude
import GraphInputsRow24Part00141Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0257
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 31929349967936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record000_result⟩)
 (.leaf ⟨(24, 31961603670272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 31973012701440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 31994356498688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record003_result⟩)
 (.leaf ⟨(24, 31994629128192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 31994901692416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 31995091550208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record006_result⟩)
 (.leaf ⟨(24, 32011536367616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 32011808931840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 32012271353856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record009_result⟩)
 (.leaf ⟨(24, 32012337414144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11788 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 11788 11799 :=
  block_of_table results 11788 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0257
