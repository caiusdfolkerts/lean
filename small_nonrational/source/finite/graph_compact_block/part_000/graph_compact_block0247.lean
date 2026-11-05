module
prelude
import GraphInputsRow24Part00131Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0247
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 31514897219584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31520799654144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record001_result⟩)
 (.leaf ⟨(24, 31521914290176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31522451095552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record003_result⟩)
 (.leaf ⟨(24, 31526202933504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31526537461760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record005_result⟩)
 (.leaf ⟨(24, 31526743965696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 31528419655680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 31528692219904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record008_result⟩)
 (.leaf ⟨(24, 31529220702208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 31529389555968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record010_result⟩)
 (.leaf ⟨(24, 31530160226848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 31530160758784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record012_result⟩)
 (.leaf ⟨(24, 31530500030464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00131.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11662 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 11662 11676 :=
  block_of_table results 11662 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0247
