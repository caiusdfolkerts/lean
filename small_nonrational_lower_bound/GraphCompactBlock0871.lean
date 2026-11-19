module
prelude
import GraphInputsRow31Part00083Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0871
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 16774032588800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record000_result⟩)
 (.leaf ⟨(31, 16774800605184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 16778961354752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 16785875173376), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record003_result⟩)
 (.leaf ⟨(31, 16786011455488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 16786915360768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record005_result⟩)
 (.leaf ⟨(31, 16823387062272), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 16907277238272), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 16930761081348), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record008_result⟩)
 (.leaf ⟨(31, 16930830286848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 16943922806784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record010_result⟩)
 (.leaf ⟨(31, 16952772788224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 16965255036928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record012_result⟩)
 (.branch 14
 (.leaf ⟨(31, 16969415786496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record013_result⟩)
 (.leaf ⟨(31, 17043521306880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(31, 17043541786880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record015_result⟩)
 (.branch 17
 (.leaf ⟨(31, 17043558563840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record016_result⟩)
 (.leaf ⟨(31, 17043566886912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(31, 17043776667904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record018_result⟩)
 (.branch 20
 (.leaf ⟨(31, 17043789774848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record019_result⟩)
 (.leaf ⟨(31, 17043798097920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26153 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 26153 26174 :=
  block_of_table results 26153 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0871
