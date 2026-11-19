module
prelude
import GraphInputsRow24Part00039Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0155
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 17300933836800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 17308718399488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record001_result⟩)
 (.leaf ⟨(24, 17326193774592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 17328448798720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record003_result⟩)
 (.leaf ⟨(24, 17361742594048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 17429270888448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record005_result⟩)
 (.leaf ⟨(24, 17455890071808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 17458106793984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 17458379358208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record008_result⟩)
 (.leaf ⟨(24, 17461227356160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 17461995372544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record010_result⟩)
 (.leaf ⟨(24, 17464620482560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 17466156122112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record012_result⟩)
 (.leaf ⟨(24, 17469821419520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9423 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 9423 9437 :=
  block_of_table results 9423 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0155
