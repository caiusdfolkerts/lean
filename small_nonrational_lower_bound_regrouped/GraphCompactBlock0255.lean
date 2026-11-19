module
prelude
import GraphInputsRow24Part00139Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0255
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 31784924381440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31785060728832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record001_result⟩)
 (.leaf ⟨(24, 31785069051904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31785308454912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record003_result⟩)
 (.leaf ⟨(24, 31787070816512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31787339284480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record005_result⟩)
 (.leaf ⟨(24, 31787347607552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 31787388829696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 31787858534400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record008_result⟩)
 (.leaf ⟨(24, 31789200605440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 31790005748224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record010_result⟩)
 (.leaf ⟨(24, 31795643031808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 31812822900736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record012_result⟩)
 (.leaf ⟨(24, 31812890001408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00139.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11746 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 11746 11760 :=
  block_of_table results 11746 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0255
