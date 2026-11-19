module
prelude
import GraphInputsRow24Part00149Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0265
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 32474801930496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32474806157312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record001_result⟩)
 (.leaf ⟨(24, 32474813960192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 32475053297920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 32476126774016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_result⟩)
 (.leaf ⟨(24, 32487535546624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 32487692570624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 32488609022720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record007_result⟩)
 (.leaf ⟨(24, 32489315795200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 32492232901136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record009_result⟩)
 (.leaf ⟨(24, 32506745782528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 32507014185216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record011_result⟩)
 (.leaf ⟨(24, 32507026214912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11882 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 11882 11895 :=
  block_of_table results 11882 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0265
