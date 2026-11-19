module
prelude
import GraphInputsRow30Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0752
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 12147650265088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record000_result⟩)
 (.leaf ⟨(30, 12147654426624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 12147914473600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 12151134126208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record003_result⟩)
 (.leaf ⟨(30, 12151268327552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 12165786374400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record005_result⟩)
 (.leaf ⟨(30, 12167932809472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 12173625556992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 12176848850944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record008_result⟩)
 (.leaf ⟨(30, 12181947056128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 12245566230528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record010_result⟩)
 (.leaf ⟨(30, 12250532315136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 12250992623744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 12320784777856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record013_result⟩)
 (.leaf ⟨(30, 12376363503616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(30, 12376619909248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record015_result⟩)
 (.leaf ⟨(30, 12380656373760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record016_result⟩))
 (.branch 18
 (.leaf ⟨(30, 12380914860160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 12382802808832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record018_result⟩)
 (.leaf ⟨(30, 12447958204672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 12448495075328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record020_result⟩)
 (.leaf ⟨(30, 12465138073600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 12465274355712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record022_result⟩)
 (.branch 24
 (.leaf ⟨(30, 12546270855168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record023_result⟩)
 (.leaf ⟨(30, 12554600448000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(30, 12577830633728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record025_result⟩)
 (.leaf ⟨(30, 12577966981120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record026_result⟩))
 (.branch 28
 (.leaf ⟨(30, 12577975304192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 12578107424768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record028_result⟩)
 (.leaf ⟨(30, 12578214707200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(30, 12578367504384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record030_result⟩)
 (.leaf ⟨(30, 12578371665920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record031_result⟩))
 (.branch 33
 (.leaf ⟨(30, 12578483109888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 12584810971136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record033_result⟩)
 (.leaf ⟨(30, 12586812702720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(30, 12592861954176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record035_result⟩)
 (.leaf ⟨(30, 12593045733376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record036_result⟩))
 (.branch 38
 (.leaf ⟨(30, 12594991743104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record037_result⟩)
 (.branch 39
 (.leaf ⟨(30, 12645748969728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record038_result⟩)
 (.leaf ⟨(30, 12648968622336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00024.record039_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24272 + i))) 0 40 :=
  interval_of_check _ 0 40 (by decide +kernel)

public theorem complete : Block 24272 24312 :=
  block_of_table results 24272 40 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0752
