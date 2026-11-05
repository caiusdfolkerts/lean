module
prelude
import GraphInputsRow31Part00096Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0884
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 20079777947712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record000_result⟩)
 (.leaf ⟨(31, 20420825251840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 20466328666112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 20534913925120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record003_result⟩)
 (.leaf ⟨(31, 20567126179840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(31, 20732083961856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record005_result⟩)
 (.branch 7
 (.leaf ⟨(31, 20732612444160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record006_result⟩)
 (.leaf ⟨(31, 20740669702144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(31, 20744830451712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record008_result⟩)
 (.branch 10
 (.leaf ⟨(31, 20749255442432), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record009_result⟩)
 (.leaf ⟨(31, 20828720726016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00096.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26308 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 26308 26319 :=
  block_of_table results 26308 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0884
