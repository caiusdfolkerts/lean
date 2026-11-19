module
prelude
import GraphInputsRow31Part00118Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0906
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 26513639505920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 26535995129856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record001_result⟩)
 (.leaf ⟨(31, 26537035317248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 26571360583680), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 26571622645760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record004_result⟩)
 (.leaf ⟨(31, 26580210418240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 26616718696448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 26716980412544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record007_result⟩)
 (.leaf ⟨(31, 26717248847872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(31, 26717253009408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record009_result⟩)
 (.branch 11
 (.leaf ⟨(31, 26757714428032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record010_result⟩)
 (.leaf ⟨(31, 27015630037248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26469 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 26469 26481 :=
  block_of_table results 26469 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0906
