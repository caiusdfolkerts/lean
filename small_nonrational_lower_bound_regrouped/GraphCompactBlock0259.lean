module
prelude
import GraphInputsRow24Part00143Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0259
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 32059313897728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32074916708608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record001_result⟩)
 (.leaf ⟨(24, 32075371003904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 32076493488704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record003_result⟩)
 (.leaf ⟨(24, 32076512362496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 32078037139712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record005_result⟩)
 (.leaf ⟨(24, 32078171406336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 32078179729408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record007_result⟩)
 (.leaf ⟨(24, 32078574010368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 32078708081152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record009_result⟩)
 (.leaf ⟨(24, 32163157250112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 32163421491264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record011_result⟩)
 (.leaf ⟨(24, 32164039131392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 32164049600512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record013_result⟩)
 (.leaf ⟨(24, 32164247781376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11806 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 11806 11821 :=
  block_of_table results 11806 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0259
