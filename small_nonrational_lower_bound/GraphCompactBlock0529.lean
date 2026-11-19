module
prelude
import GraphInputsRow29Part00095Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0529
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 16632824991744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record000_result⟩)
 (.leaf ⟨(29, 16640383188992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 16640391512064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record002_result⟩)
 (.leaf ⟨(29, 16641522466816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 16648436220160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record004_result⟩)
 (.leaf ⟨(29, 16648572567552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 16648580890624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record006_result⟩)
 (.leaf ⟨(29, 16648704688128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 16648713011200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record008_result⟩)
 (.leaf ⟨(29, 16649173352448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 16649476407552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record010_result⟩)
 (.leaf ⟨(29, 16650111812112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 16650246569984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record012_result⟩)
 (.leaf ⟨(29, 16678037487616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 16686086422528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record014_result⟩)
 (.leaf ⟨(29, 16701118808320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21834 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 21834 21850 :=
  block_of_table results 21834 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0529
