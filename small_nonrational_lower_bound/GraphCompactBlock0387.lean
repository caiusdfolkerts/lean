module
prelude
import GraphInputsRow26Part00071Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0387
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 32012271353856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record000_result⟩)
 (.leaf ⟨(26, 32012337414144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 32025986732096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record002_result⟩)
 (.leaf ⟨(26, 32026600210688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 32027077263360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record004_result⟩)
 (.leaf ⟨(26, 32043780079616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 32044316884992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 32059272740864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record007_result⟩)
 (.leaf ⟨(26, 32075371003904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 32076493488704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record009_result⟩)
 (.leaf ⟨(26, 32076512362496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 32078179729408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 32078574010368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record012_result⟩)
 (.leaf ⟨(26, 32163157250112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(26, 32163421491264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record014_result⟩)
 (.leaf ⟨(26, 32164039131392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record015_result⟩))
 (.branch 17
 (.leaf ⟨(26, 32164049600512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 32164247781376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record017_result⟩)
 (.leaf ⟨(26, 32172629098496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17374 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 17374 17393 :=
  block_of_table results 17374 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0387
