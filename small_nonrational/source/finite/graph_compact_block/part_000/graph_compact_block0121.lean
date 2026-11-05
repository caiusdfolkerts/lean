module
prelude
import GraphInputsRow24Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0121
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 3157606269568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record000_result⟩)
 (.leaf ⟨(24, 3164726165760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 3164730327296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 3164730392576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record003_result⟩)
 (.leaf ⟨(24, 3164998762624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 3165000843392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record005_result⟩)
 (.leaf ⟨(24, 3166678646784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 3166806540544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 3166810702080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record008_result⟩)
 (.leaf ⟨(24, 3166810767360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 3166876762368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record010_result⟩)
 (.leaf ⟨(24, 3166876827648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 3167079137408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 3167081218176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record013_result⟩)
 (.leaf ⟨(24, 3167850954752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 3174392471552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 3188151320576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record016_result⟩)
 (.leaf ⟨(24, 3191263494400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 3191267721216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 3191271882752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record019_result⟩)
 (.leaf ⟨(24, 3191333781504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8026 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 8026 8047 :=
  block_of_table results 8026 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0121
