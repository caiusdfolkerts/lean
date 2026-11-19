module
prelude
import GraphInputsRow24Part00068Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0184
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 23422404919296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 23425894596864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record001_result⟩)
 (.leaf ⟨(24, 23426028863488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 23426037186560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 23426431467520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record004_result⟩)
 (.leaf ⟨(24, 23426497527808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 23429081219328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 23429149425664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record007_result⟩)
 (.leaf ⟨(24, 23429157748736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 23429618089984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 23436900499712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record010_result⟩)
 (.leaf ⟨(24, 23437168902400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10328 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 10328 10340 :=
  block_of_table results 10328 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0184
