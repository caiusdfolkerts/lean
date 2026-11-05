module
prelude
import GraphInputsRow26Part00069Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0385
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 31752023244800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 31753835151616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record001_result⟩)
 (.leaf ⟨(26, 31754103619584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 31754111942656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record003_result⟩)
 (.leaf ⟨(26, 31754573324288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 31754875339008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record005_result⟩)
 (.leaf ⟨(26, 31755646541824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 31758264369152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record007_result⟩)
 (.leaf ⟨(26, 31758272692224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 31761317765376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record009_result⟩)
 (.leaf ⟨(26, 31763465306112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 31763539689472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record011_result⟩)
 (.leaf ⟨(26, 31764002111488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 31778497634304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record013_result⟩)
 (.leaf ⟨(26, 31778564734976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00069.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17319 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 17319 17334 :=
  block_of_table results 17319 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0385
