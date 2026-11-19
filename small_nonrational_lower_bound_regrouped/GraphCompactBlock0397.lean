module
prelude
import GraphInputsRow26Part00081Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0397
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 34088358645824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 34088394162177), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record001_result⟩)
 (.leaf ⟨(26, 34090398023936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 34093561546768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record003_result⟩)
 (.leaf ⟨(26, 34094007193616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 34094023968784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record005_result⟩)
 (.leaf ⟨(26, 34095097708545), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 34119375655168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record007_result⟩)
 (.leaf ⟨(26, 34119514067008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 34123792123920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record009_result⟩)
 (.leaf ⟨(26, 34123809292289), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 34124794494976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record011_result⟩)
 (.leaf ⟨(26, 34124865863681), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 34127952873488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record013_result⟩)
 (.leaf ⟨(26, 34155878973696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17577 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 17577 17592 :=
  block_of_table results 17577 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0397
