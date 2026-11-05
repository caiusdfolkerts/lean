module
prelude
import GraphInputsRow29Part00097Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0531
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 16770259750912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 16776699056128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record001_result⟩)
 (.leaf ⟨(29, 16778692984832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 16778960830992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 16784933785728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record004_result⟩)
 (.leaf ⟨(29, 16815208005632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 16906134257920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 16908350980096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record007_result⟩)
 (.leaf ⟨(29, 16908623544320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 16909019906048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 16914724225024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record010_result⟩)
 (.leaf ⟨(29, 16915261030400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(29, 16930795700224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 16931904028672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record013_result⟩)
 (.leaf ⟨(29, 16932036149248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(29, 16943667019776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 16943939584000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record016_result⟩)
 (.leaf ⟨(29, 16944451551232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(29, 16947959889920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 16948496695296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record019_result⟩)
 (.leaf ⟨(29, 16948612300800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(29, 16952236113920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record021_result⟩)
 (.branch 23
 (.leaf ⟨(29, 16969415917568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record022_result⟩)
 (.leaf ⟨(29, 16975996715008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00097.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21857 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 21857 21881 :=
  block_of_table results 21857 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0531
