module
prelude
import GraphInputsRow26Part00061Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0377
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 29068423872640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record000_result⟩)
 (.leaf ⟨(26, 29138218483840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 29138220564608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record002_result⟩)
 (.leaf ⟨(26, 29138224726144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 29138426028160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record004_result⟩)
 (.leaf ⟨(26, 29138690818064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 29139361370368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 29139361403008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record007_result⟩)
 (.leaf ⟨(26, 29139361431568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 29139378178176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record009_result⟩)
 (.leaf ⟨(26, 29139493490944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 29139493523584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record011_result⟩)
 (.leaf ⟨(26, 29139493552144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(26, 29139495632912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record013_result⟩)
 (.leaf ⟨(26, 29139499794448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record014_result⟩))
 (.branch 16
 (.leaf ⟨(26, 29139516309520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 29145757433872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record016_result⟩)
 (.leaf ⟨(26, 29145934876928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 29145958735888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record018_result⟩)
 (.leaf ⟨(26, 29147029061888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 29147063652608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record020_result⟩)
 (.leaf ⟨(26, 29171573424144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 29171707625488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record022_result⟩)
 (.leaf ⟨(26, 29171711787024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 29175985670160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 29180146419728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record025_result⟩)
 (.leaf ⟨(26, 29180297756928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(26, 29180299317504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record027_result⟩)
 (.leaf ⟨(26, 29215783190528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record028_result⟩))
 (.branch 30
 (.leaf ⟨(26, 29274583433232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 29274585514000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record030_result⟩)
 (.leaf ⟨(26, 29274589675536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 29274790977552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_result⟩)
 (.leaf ⟨(26, 29276783183888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 29276936081664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 29283156428816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record035_result⟩)
 (.leaf ⟨(26, 29284463821056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17054 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 17054 17091 :=
  block_of_table results 17054 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0377
