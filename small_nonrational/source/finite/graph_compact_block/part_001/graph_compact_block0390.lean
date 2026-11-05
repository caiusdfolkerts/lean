module
prelude
import GraphInputsRow26Part00074Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0390
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 32513456611584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record000_result⟩)
 (.leaf ⟨(26, 32513464999936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 32513465520128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record002_result⟩)
 (.leaf ⟨(26, 32514521571328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 32514547712000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record004_result⟩)
 (.leaf ⟨(26, 32521828176128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 32522051260416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 32522297937952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record007_result⟩)
 (.leaf ⟨(26, 32523371414048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 32524445155856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record009_result⟩)
 (.leaf ⟨(26, 32531727515648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 32643379953664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record011_result⟩)
 (.leaf ⟨(26, 32643388276736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(26, 32658948628736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record013_result⟩)
 (.leaf ⟨(26, 32659032309760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record014_result⟩))
 (.branch 16
 (.leaf ⟨(26, 32659485499392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 32659486539776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record016_result⟩)
 (.leaf ⟨(26, 32659502014464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00074.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17441 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 17441 17459 :=
  block_of_table results 17441 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0390
