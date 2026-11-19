module
prelude
import GraphInputsRow24Part00169Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0285
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 34638009532416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record000_result⟩)
 (.leaf ⟨(24, 34638017855488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 34638240743424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 34639196983552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record003_result⟩)
 (.leaf ⟨(24, 34639205371904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 34639213498624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 34640286974720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record006_result⟩)
 (.leaf ⟨(24, 34641092837632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 34641864560640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 34670085439744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record009_result⟩)
 (.leaf ⟨(24, 34673288315136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12084 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 12084 12095 :=
  block_of_table results 12084 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0285
