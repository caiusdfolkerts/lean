module
prelude
import GraphInputsRow24Part00146Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0262
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 32236682878976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32266097065984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record001_result⟩)
 (.leaf ⟨(24, 32266105389056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 32268107153664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 32268425166848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record004_result⟩)
 (.leaf ⟨(24, 32268894871552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 32271042085376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 32299321147392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record007_result⟩)
 (.leaf ⟨(24, 32300394364928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 32300402491648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 32300856786944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record010_result⟩)
 (.leaf ⟨(24, 32301979271744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11838 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 11838 11850 :=
  block_of_table results 11838 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0262
