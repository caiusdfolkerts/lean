module
prelude
import GraphInputsRow29Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0441
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 2036110262272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 2036217479424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record001_result⟩)
 (.leaf ⟨(29, 2036370276608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 2036374503424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record003_result⟩)
 (.leaf ⟨(29, 2036485882112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 2036498171904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record005_result⟩)
 (.leaf ⟨(29, 2040914772736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 2040923226112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record007_result⟩)
 (.leaf ⟨(29, 2049508966400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 2049517289472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record009_result⟩)
 (.leaf ⟨(29, 2053132845312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 2057289498880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record011_result⟩)
 (.leaf ⟨(29, 2057557966848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 2057566224384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record013_result⟩)
 (.leaf ⟨(29, 2057566289920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00007.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20598 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 20598 20613 :=
  block_of_table results 20598 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0441
