module
prelude
import GraphInputsRow24Part00051Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0167
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 19659485151232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 19660525338624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record001_result⟩)
 (.leaf ⟨(24, 19664048504832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 19672370003968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 19676051021888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record004_result⟩)
 (.leaf ⟨(24, 19680825704448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 19681286045696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 19683869737216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record007_result⟩)
 (.leaf ⟨(24, 19683937943552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 19683946266624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 19684012326912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_result⟩)
 (.leaf ⟨(24, 19684045357056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9764 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 9764 9776 :=
  block_of_table results 9764 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0167
