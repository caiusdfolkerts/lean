module
prelude
import GraphInputsRow24Part00111Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0227
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27678649368640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record000_result⟩)
 (.leaf ⟨(24, 27680395296768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27681870061632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 27682351874048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record003_result⟩)
 (.leaf ⟨(24, 27682475671552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 27682483994624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record005_result⟩)
 (.leaf ⟨(24, 27686502154496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 27686636421120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 27686644744192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record008_result⟩)
 (.leaf ⟨(24, 27687039025152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00111.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11216 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 11216 11226 :=
  block_of_table results 11216 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0227
