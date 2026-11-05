module
prelude
import GraphInputsRow29Part00237Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0671
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 31482664460544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record000_result⟩)
 (.leaf ⟨(29, 31482672848896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 31483729420288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 31483788002048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record003_result⟩)
 (.leaf ⟨(29, 31491505786912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 31491843195136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 31492109501184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record006_result⟩)
 (.leaf ⟨(29, 31492177723392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 31492579263008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 31495029817600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record009_result⟩)
 (.leaf ⟨(29, 31495801020416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23302 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 23302 23313 :=
  block_of_table results 23302 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0671
