module
prelude
import GraphInputsRow24Part00074Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0190
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 23990114516992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record000_result⟩)
 (.leaf ⟨(24, 24004606853376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 24005717327872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 24005989892096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record003_result⟩)
 (.leaf ⟨(24, 24006452314112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 24017742659840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record005_result⟩)
 (.leaf ⟨(24, 24017751048192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 24018011062528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 24018023352320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record008_result⟩)
 (.leaf ⟨(24, 24018262690048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 24021773123840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record010_result⟩)
 (.leaf ⟨(24, 24022309994496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 24024176459776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 24026584058112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record013_result⟩)
 (.leaf ⟨(24, 24026592446464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 24026600702720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record015_result⟩)
 (.leaf ⟨(24, 24034913945600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 24035442295304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 24041356263424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record018_result⟩)
 (.leaf ⟨(24, 24041884745728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00074.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10463 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 10463 10483 :=
  block_of_table results 10463 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0190
