module
prelude
import GraphInputsRow29Part00146Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0580
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24455613054976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record000_result⟩)
 (.leaf ⟨(29, 24457833873408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24458362355712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record002_result⟩)
 (.leaf ⟨(29, 24470778052864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 24477421805824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record004_result⟩)
 (.leaf ⟨(29, 24477824458816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 24482591834112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 24482796281856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record007_result⟩)
 (.leaf ⟨(29, 24504067751936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00146.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22579 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22579 22588 :=
  block_of_table results 22579 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0580
