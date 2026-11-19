module
prelude
import GraphInputsRow24Part00116Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0232
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27939056926720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_result⟩)
 (.leaf ⟨(24, 27939098083584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27941312398080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record002_result⟩)
 (.leaf ⟨(24, 27943258833152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 27943269042176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_result⟩)
 (.leaf ⟨(24, 27943661486144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 27943728586816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record006_result⟩)
 (.leaf ⟨(24, 27971269181440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 27971310338304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record008_result⟩)
 (.leaf ⟨(24, 28041076080896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 28041080242432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record010_result⟩)
 (.leaf ⟨(24, 28041080307712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 28041082323200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record012_result⟩)
 (.leaf ⟨(24, 28047521628416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 28047785869568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 28047785934848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record015_result⟩)
 (.leaf ⟨(24, 28076495437824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11283 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 11283 11300 :=
  block_of_table results 11283 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0232
