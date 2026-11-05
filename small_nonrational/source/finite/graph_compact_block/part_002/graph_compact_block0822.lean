module
prelude
import GraphInputsRow31Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0822
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 7295673630720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 7297754005504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record001_result⟩)
 (.leaf ⟨(31, 7302587384064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 7302723731456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 7302732054528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record004_result⟩)
 (.leaf ⟨(31, 7302864175104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 7303627571456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 7331509371136), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record007_result⟩)
 (.leaf ⟨(31, 7340099272960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(31, 7340904415744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record009_result⟩)
 (.branch 11
 (.leaf ⟨(31, 7340912803840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record010_result⟩)
 (.leaf ⟨(31, 7372311527680), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25764 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 25764 25776 :=
  block_of_table results 25764 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0822
