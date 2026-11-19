module
prelude
import GraphInputsRow31Part00103Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0891
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 23424888012800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record000_result⟩)
 (.leaf ⟨(31, 23455622758400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 23459180642304), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 23504344908032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record003_result⟩)
 (.leaf ⟨(31, 23768894275584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(31, 23971017785344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record005_result⟩)
 (.branch 7
 (.leaf ⟨(31, 23974650052608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record006_result⟩)
 (.leaf ⟨(31, 24043763793920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(31, 24054107013120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record008_result⟩)
 (.branch 10
 (.leaf ⟨(31, 24091016822784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record009_result⟩)
 (.leaf ⟨(31, 24108188303360), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26362 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 26362 26373 :=
  block_of_table results 26362 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0891
