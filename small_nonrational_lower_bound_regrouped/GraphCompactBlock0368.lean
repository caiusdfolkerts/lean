module
prelude
import GraphInputsRow26Part00052Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0368
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 25431064449088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record000_result⟩)
 (.leaf ⟨(26, 25432146592000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 25443598075920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record002_result⟩)
 (.leaf ⟨(26, 25443943059520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 25445031493696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record004_result⟩)
 (.leaf ⟨(26, 25449326460928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 25496554324224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 25512676433984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record007_result⟩)
 (.leaf ⟨(26, 25566088532032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 25566352773184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record009_result⟩)
 (.leaf ⟨(26, 25568499208256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 25569317110016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record011_result⟩)
 (.leaf ⟨(26, 25572792078400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(26, 25573880512576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record013_result⟩)
 (.leaf ⟨(26, 25578175479808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record014_result⟩))
 (.branch 16
 (.leaf ⟨(26, 25581032835088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 25582106574849), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record016_result⟩)
 (.leaf ⟨(26, 25590657728512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 25633724842240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record018_result⟩)
 (.leaf ⟨(26, 25634244141120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 25641525452864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record020_result⟩)
 (.leaf ⟨(26, 25658186022912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 25659208507456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record022_result⟩)
 (.leaf ⟨(26, 25659275624448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 25659277705216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 25659409695232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record025_result⟩)
 (.leaf ⟨(26, 25702244040960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(26, 25702252429312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record027_result⟩)
 (.leaf ⟨(26, 25702310101248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record028_result⟩))
 (.branch 30
 (.leaf ⟨(26, 25702312247296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 25702318489600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record030_result⟩)
 (.leaf ⟨(26, 25702359646464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 25702369855488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record032_result⟩)
 (.leaf ⟨(26, 25702712754240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 25702714851328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 25702762299456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record035_result⟩)
 (.leaf ⟨(26, 25702829400128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00052.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16706 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 16706 16743 :=
  block_of_table results 16706 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0368
