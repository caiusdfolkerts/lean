module
prelude
import GraphInputsRow26Part00080Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0396
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 33687073718272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 33742623145984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record001_result⟩)
 (.leaf ⟨(26, 33742631469056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 33742672691200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 33750423707648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record004_result⟩)
 (.leaf ⟨(26, 33750926893312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 33751530734080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 34086020743424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record007_result⟩)
 (.leaf ⟨(26, 34086020808704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 34086022824192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 34086022889472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record010_result⟩)
 (.leaf ⟨(26, 34086228336704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 34086228353024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 34086228856896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record013_result⟩)
 (.leaf ⟨(26, 34087163662592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 34087163727872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 34087171526672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record016_result⟩)
 (.leaf ⟨(26, 34087180177664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 34087180242944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 34087188301840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record019_result⟩)
 (.leaf ⟨(26, 34087302074432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 34087303647248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record021_result⟩)
 (.leaf ⟨(26, 34087320422416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 34088253719040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record023_result⟩)
 (.leaf ⟨(26, 34088262041601), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00080.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17552 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 17552 17577 :=
  block_of_table results 17552 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0396
