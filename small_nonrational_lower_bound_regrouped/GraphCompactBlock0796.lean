module
prelude
import GraphInputsRow31Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0796
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 1393058390080), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record000_result⟩)
 (.leaf ⟨(31, 1422317846529), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 1430907813888), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 1431031546112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record003_result⟩)
 (.leaf ⟨(31, 1431042015232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(31, 1435326497024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record005_result⟩)
 (.branch 7
 (.leaf ⟨(31, 1469685186816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record006_result⟩)
 (.leaf ⟨(31, 1765508448512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(31, 1766045319168), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record008_result⟩)
 (.branch 10
 (.leaf ⟨(31, 1774094188800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record009_result⟩)
 (.leaf ⟨(31, 1774631059456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25523 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 25523 25534 :=
  block_of_table results 25523 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0796
