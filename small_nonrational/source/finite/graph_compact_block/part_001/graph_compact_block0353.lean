module
prelude
import GraphInputsRow26Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0353
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 20727650715904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 20727650781184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record001_result⟩)
 (.leaf ⟨(26, 20727654910080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 20727791092744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 20727803740160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record004_result⟩)
 (.leaf ⟨(26, 20727807868929), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 20728055333896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 20728072110081), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record007_result⟩)
 (.leaf ⟨(26, 20736240650368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 20748987139200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 20748991333376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record010_result⟩)
 (.leaf ⟨(26, 20749255442948), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 20754567530624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 20756912209920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record013_result⟩)
 (.leaf ⟨(26, 20757688092800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 20757754153088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 20758992584704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record016_result⟩)
 (.leaf ⟨(26, 20760032772096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 20770632763520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 20787795099904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record019_result⟩)
 (.leaf ⟨(26, 20787803195520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(26, 20792079419520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 20792228249600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record022_result⟩)
 (.leaf ⟨(26, 20796634579200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(26, 20800929268480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 20822095825024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record025_result⟩)
 (.leaf ⟨(26, 20822161885312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(26, 20822558247040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 20824291674240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record028_result⟩)
 (.leaf ⟨(26, 20824440504320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 20826372049024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 20839250659456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record031_result⟩)
 (.leaf ⟨(26, 20894120493184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(26, 20896663289984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 20930862547200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record034_result⟩)
 (.leaf ⟨(26, 20930862612480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(26, 20935157498112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 20935157563392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record037_result⟩)
 (.leaf ⟨(26, 20938378711296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(26, 20938649243712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 20961747878016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record040_result⟩)
 (.leaf ⟨(26, 20969714434048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(26, 21007368716289), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 21035015475456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record043_result⟩)
 (.leaf ⟨(26, 21046621192192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 21046826639424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record045_result⟩)
 (.leaf ⟨(26, 21047900377152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 21076086095873), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record047_result⟩)
 (.leaf ⟨(26, 21111452467200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00037.record048_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15988 + i))) 0 49 :=
  interval_of_check _ 0 49 (by decide +kernel)

public theorem complete : Block 15988 16037 :=
  block_of_table results 15988 49 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0353
