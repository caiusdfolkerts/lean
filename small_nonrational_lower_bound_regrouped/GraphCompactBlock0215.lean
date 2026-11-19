module
prelude
import GraphInputsRow24Part00099Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0215
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25428918014016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_result⟩)
 (.leaf ⟨(24, 25431058157824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25431064449088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 25432146592000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record003_result⟩)
 (.leaf ⟨(24, 25443598075920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 25443943059520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 25444671815681), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record006_result⟩)
 (.leaf ⟨(24, 25445031493696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 25449326460928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 25496554324224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record009_result⟩)
 (.leaf ⟨(24, 25512676433984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 25565950120192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record011_result⟩)
 (.leaf ⟨(24, 25565956411456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 25566088532032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 25566352773184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record014_result⟩)
 (.leaf ⟨(24, 25568228675840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 25568234967104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 25568499208256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record017_result⟩)
 (.leaf ⟨(24, 25569317110016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 25572792078400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 25573880512576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record020_result⟩)
 (.leaf ⟨(24, 25578175479808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10945 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 10945 10967 :=
  block_of_table results 10945 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0215
