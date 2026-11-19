module
prelude
import GraphInputsRow26Part00079Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0395
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 33158515933184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record000_result⟩)
 (.leaf ⟨(26, 33167415181888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 33195132256256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record002_result⟩)
 (.leaf ⟨(26, 33197212631040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 33204426776832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record004_result⟩)
 (.leaf ⟨(26, 33205534130176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 33206070935552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record006_result⟩)
 (.leaf ⟨(26, 33206574317568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 33206648700928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record008_result⟩)
 (.leaf ⟨(26, 33207111122944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 33230448295936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record010_result⟩)
 (.leaf ⟨(26, 33230456619008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 33241436389376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record012_result⟩)
 (.leaf ⟨(26, 33261385957504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 33294638137472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record014_result⟩)
 (.leaf ⟨(26, 33294638170112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 33295733621768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_result⟩)
 (.leaf ⟨(26, 33295750397953), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 33538634219520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record018_result⟩)
 (.leaf ⟨(26, 33540780654592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 33545073524736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record020_result⟩)
 (.leaf ⟨(26, 33545171509504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 33546245247232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record022_result⟩)
 (.leaf ⟨(26, 33574049349632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 33578342219776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record024_result⟩)
 (.leaf ⟨(26, 33578457239808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 33579530715904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record026_result⟩)
 (.leaf ⟨(26, 33612699803904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 33612749869312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record028_result⟩)
 (.leaf ⟨(26, 33613790904320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 33677124313344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 33678215413760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record031_result⟩)
 (.leaf ⟨(26, 33681335128320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17519 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 17519 17552 :=
  block_of_table results 17519 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0395
