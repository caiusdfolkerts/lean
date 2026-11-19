module
prelude
import GraphInputsRow24Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0118
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 1027103293696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record000_result⟩)
 (.leaf ⟨(24, 1027111682048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 1050736083072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 1225353428992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record003_result⟩)
 (.leaf ⟨(24, 1225749790720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 1226018193408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record005_result⟩)
 (.leaf ⟨(24, 1226026516480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 1229646233856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 1232832921600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record008_result⟩)
 (.leaf ⟨(24, 1329403560192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 1329502650624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record010_result⟩)
 (.leaf ⟨(24, 1363794952192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 1422919762176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 1438984995072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record013_result⟩)
 (.leaf ⟨(24, 1501365798144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 1501506371584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 1501898506496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record016_result⟩)
 (.leaf ⟨(24, 1502034853888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 1502043176960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 1506067644416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record019_result⟩)
 (.leaf ⟨(24, 1507602891008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00002.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7851 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 7851 7872 :=
  block_of_table results 7851 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0118
