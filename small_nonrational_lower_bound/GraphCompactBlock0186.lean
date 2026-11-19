module
prelude
import GraphInputsRow24Part00070Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0186
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 23461370003456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 23470004044032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record001_result⟩)
 (.leaf ⟨(24, 23470012432384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 23470136164608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 23470144552960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record004_result⟩)
 (.leaf ⟨(24, 23470251770112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 23470404567296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 23470408794112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record007_result⟩)
 (.leaf ⟨(24, 23470415036416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 23474819104768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record009_result⟩)
 (.leaf ⟨(24, 23476492894464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 23476845953280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record011_result⟩)
 (.leaf ⟨(24, 23476848099328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 23476854341632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 23476895498496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record014_result⟩)
 (.leaf ⟨(24, 23476905707520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 23485095086080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record016_result⟩)
 (.leaf ⟨(24, 23485216997632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 23485227206656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record018_result⟩)
 (.leaf ⟨(24, 23485440081920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(24, 23485686751296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 23491600580608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record021_result⟩)
 (.leaf ⟨(24, 23495753007104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 23495761330176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record023_result⟩)
 (.leaf ⟨(24, 23496155611136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 23505485758720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record025_result⟩)
 (.leaf ⟨(24, 23505494147072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00070.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10344 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 10344 10371 :=
  block_of_table results 10344 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0186
