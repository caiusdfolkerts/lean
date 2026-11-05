module
prelude
import GraphInputsRow24Part00137Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0253
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 31751825063936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record000_result⟩)
 (.leaf ⟨(24, 31751833387008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 31752023244800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 31753835151616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record003_result⟩)
 (.leaf ⟨(24, 31754103619584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 31754111942656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 31754573324288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record006_result⟩)
 (.leaf ⟨(24, 31754875339008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 31755646541824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 31758264369152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record009_result⟩)
 (.leaf ⟨(24, 31758272692224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11729 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 11729 11740 :=
  block_of_table results 11729 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0253
