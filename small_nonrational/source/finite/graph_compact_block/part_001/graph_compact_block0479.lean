module
prelude
import GraphInputsRow29Part00045Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0479
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 8045883032320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 8046155726848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record001_result⟩)
 (.leaf ⟨(29, 8046164049920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 8066754953216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 8156822372352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record004_result⟩)
 (.leaf ⟨(29, 8164871307264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 8165540233216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 8173465370624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record007_result⟩)
 (.leaf ⟨(29, 8173993852928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 8179903693056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 8184337072128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record010_result⟩)
 (.leaf ⟨(29, 8184873877504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(29, 8188497821696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 8189034627072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record013_result⟩)
 (.leaf ⟨(29, 8197083561984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(29, 8197356126208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 8197752487936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record016_result⟩)
 (.leaf ⟨(29, 8203456806912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(29, 8247471800576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 8247471865856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record019_result⟩)
 (.leaf ⟨(29, 8247566729472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(29, 8247570891008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record021_result⟩)
 (.leaf ⟨(29, 8247570956288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record022_result⟩))
 (.branch 24
 (.leaf ⟨(29, 8247574532352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record023_result⟩)
 (.leaf ⟨(29, 8247970894080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21095 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 21095 21120 :=
  block_of_table results 21095 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0479
