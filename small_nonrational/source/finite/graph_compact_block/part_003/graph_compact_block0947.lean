module
prelude
import GraphInputsRow31Part00159Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0947
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 31346316607488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 31354906509312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record001_result⟩)
 (.leaf ⟨(31, 31465207234560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 31465735716864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 31483796389888), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record004_result⟩)
 (.leaf ⟨(31, 31490717524224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 31491254394880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 31491774095616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record007_result⟩)
 (.leaf ⟨(31, 31492117889024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(31, 31492377936384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record009_result⟩)
 (.branch 11
 (.leaf ⟨(31, 31492580311040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record010_result⟩)
 (.leaf ⟨(31, 31499324817408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26686 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 26686 26698 :=
  block_of_table results 26686 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0947
