module
prelude
import GraphInputsRow31Part00158Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0946
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 31082712932480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 31108448264448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record001_result⟩)
 (.leaf ⟨(31, 31114890723456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 31115293229568), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 31117038198912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record004_result⟩)
 (.leaf ⟨(31, 31155692904480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 31200859160832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 31224480415744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record007_result⟩)
 (.leaf ⟨(31, 31337206546688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(31, 31337218056192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record009_result⟩)
 (.branch 11
 (.leaf ⟨(31, 31337449267200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record010_result⟩)
 (.leaf ⟨(31, 31346315493920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00158.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26674 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 26674 26686 :=
  block_of_table results 26674 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0946
