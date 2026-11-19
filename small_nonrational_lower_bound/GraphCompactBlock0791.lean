module
prelude
import GraphInputsRow31Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0791
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 191943950400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_result⟩)
 (.leaf ⟨(31, 194091425856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 329246605440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record002_result⟩)
 (.leaf ⟨(31, 329248686208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 550883131776), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record004_result⟩)
 (.leaf ⟨(31, 550885212544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 661991227648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record006_result⟩)
 (.leaf ⟨(31, 661991292928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(31, 666529497344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record008_result⟩)
 (.leaf ⟨(31, 666537885696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record009_result⟩))
 (.branch 11
 (.leaf ⟨(31, 679412269312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record010_result⟩)
 (.leaf ⟨(31, 679422722049), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(31, 697204539648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record012_result⟩)
 (.leaf ⟨(31, 697472942336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record013_result⟩))
 (.branch 15
 (.leaf ⟨(31, 697473007616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record014_result⟩)
 (.leaf ⟨(31, 697475023104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25470 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 25470 25486 :=
  block_of_table results 25470 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0791
