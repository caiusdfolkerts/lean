module
prelude
import GraphInputsRow29Part00069Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0503
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 12176836821248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 12176848850944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record001_result⟩)
 (.leaf ⟨(29, 12181806547200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 12181814935552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 12181938667776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record004_result⟩)
 (.leaf ⟨(29, 12181942894592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 12181947056128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 12182013116416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record007_result⟩)
 (.leaf ⟨(29, 12183346380928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 12219987264128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 12236518068480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record010_result⟩)
 (.leaf ⟨(29, 12239192985600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(29, 12243485855744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 12245566230528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record013_result⟩)
 (.leaf ⟨(29, 12250523926784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(29, 12250528153600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 12250532315136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record016_result⟩)
 (.leaf ⟨(29, 12250992623744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(29, 12252065841280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 12279982588672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record019_result⟩)
 (.leaf ⟨(29, 12280118968320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(29, 12288572523136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record021_result⟩)
 (.branch 23
 (.leaf ⟨(29, 12314275218176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record022_result⟩)
 (.leaf ⟨(29, 12319109185792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00069.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21456 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 21456 21480 :=
  block_of_table results 21456 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0503
