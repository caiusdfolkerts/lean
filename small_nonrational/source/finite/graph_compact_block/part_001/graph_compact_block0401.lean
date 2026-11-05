module
prelude
import GraphInputsRow26Part00085Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0401
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 34681861050624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 34681895059456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record001_result⟩)
 (.leaf ⟨(26, 34682976600064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 34699074863104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 34703629619200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record004_result⟩)
 (.leaf ⟨(26, 34712462690320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 34712479334928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 34737712824576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record007_result⟩)
 (.leaf ⟨(26, 34738790268928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 34739062833152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record009_result⟩)
 (.leaf ⟨(26, 34739574800384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 34746302791680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record011_result⟩)
 (.leaf ⟨(26, 34746839597056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17644 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 17644 17657 :=
  block_of_table results 17644 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0401
