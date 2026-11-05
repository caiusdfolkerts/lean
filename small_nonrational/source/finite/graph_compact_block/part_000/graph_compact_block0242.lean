module
prelude
import GraphInputsRow24Part00126Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0242
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 31050537435136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31050809999360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record001_result⟩)
 (.leaf ⟨(24, 31051272421376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31057513545728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record003_result⟩)
 (.leaf ⟨(24, 31064534827136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31096730304640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record005_result⟩)
 (.leaf ⟨(24, 31175423885312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 31202208661504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record007_result⟩)
 (.leaf ⟨(24, 31235246145536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 31235444326400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record009_result⟩)
 (.leaf ⟨(24, 31235485483264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 31239650213888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record011_result⟩)
 (.leaf ⟨(24, 31244343575104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 31260986720256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record013_result⟩)
 (.leaf ⟨(24, 31274149347328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11562 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 11562 11577 :=
  block_of_table results 11562 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0242
