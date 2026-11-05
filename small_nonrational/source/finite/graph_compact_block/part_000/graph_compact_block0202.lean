module
prelude
import GraphInputsRow24Part00086Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0202
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 24617176547328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record000_result⟩)
 (.leaf ⟨(24, 24620162891840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 24621303210048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 24628484390976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record003_result⟩)
 (.leaf ⟨(24, 24628618608640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 24628620689408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record005_result⟩)
 (.leaf ⟨(24, 24629524578368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 24629592735744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 24629658796032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record008_result⟩)
 (.leaf ⟨(24, 24629660876800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 24638233018624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record010_result⟩)
 (.leaf ⟨(24, 24638237245440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 24638243487744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 24638367219968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record013_result⟩)
 (.leaf ⟨(24, 24638375608320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 24638482825472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 24638493034496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record016_result⟩)
 (.leaf ⟨(24, 24638885478464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 24640383680512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 24640428998912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record019_result⟩)
 (.leaf ⟨(24, 24640441288704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10690 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 10690 10711 :=
  block_of_table results 10690 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0202
