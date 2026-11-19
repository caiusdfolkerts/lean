module
prelude
import GraphInputsRow24Part00057Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0173
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 20930862547200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record000_result⟩)
 (.leaf ⟨(24, 20930862612480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 20935157498112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 20935157563392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record003_result⟩)
 (.leaf ⟨(24, 20938378711296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 20938649243712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record005_result⟩)
 (.leaf ⟨(24, 20969714434048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 21007368716289), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 21035015475456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record008_result⟩)
 (.leaf ⟨(24, 21046621192192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 21046826639424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record010_result⟩)
 (.leaf ⟨(24, 21047900377152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 21076086095873), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 21111452467200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_result⟩)
 (.leaf ⟨(24, 21119497175296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 21119633522688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 21119641845760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record016_result⟩)
 (.leaf ⟨(24, 21119765643264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 21119773966336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 21120234307584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record019_result⟩)
 (.leaf ⟨(24, 21123934715904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9972 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 9972 9993 :=
  block_of_table results 9972 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0173
