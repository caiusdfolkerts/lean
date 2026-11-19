module
prelude
import GraphInputsRow24Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0140
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 14220980649984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record000_result⟩)
 (.leaf ⟨(24, 14221443072000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 14235740471552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record002_result⟩)
 (.leaf ⟨(24, 14236277342208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 14236285665280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record004_result⟩)
 (.leaf ⟨(24, 14236475523072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 14250769678592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 14338291155200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record007_result⟩)
 (.leaf ⟨(24, 14348156145728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 14368557244672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record009_result⟩)
 (.leaf ⟨(24, 14372717994240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 14416473030656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 14451034034240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record012_result⟩)
 (.leaf ⟨(24, 14453248626720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 14484320043008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record014_result⟩)
 (.leaf ⟨(24, 14486534619136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 14486658416640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 14492899540992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record017_result⟩)
 (.leaf ⟨(24, 14554180354048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 14558605344768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record019_result⟩)
 (.leaf ⟨(24, 14564846469120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 14572330172544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record021_result⟩)
 (.leaf ⟨(24, 14589032956160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 14589569826816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record023_result⟩)
 (.leaf ⟨(24, 14589573988352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 14604525650048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record025_result⟩)
 (.branch 27
 (.leaf ⟨(24, 14605598867584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record026_result⟩)
 (.leaf ⟨(24, 14606927937536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 14613169061888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record028_result⟩)
 (.leaf ⟨(24, 14616457379841), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 14616457388032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 14623424282880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record031_result⟩)
 (.leaf ⟨(24, 14623428509696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(24, 14623432671232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record033_result⟩)
 (.leaf ⟨(24, 14623436702720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record034_result⟩))
 (.branch 36
 (.leaf ⟨(24, 14623568823296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 14623826919552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record036_result⟩)
 (.leaf ⟨(24, 14623833064448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00024.record037_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8975 + i))) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

public theorem complete : Block 8975 9013 :=
  block_of_table results 8975 38 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0140
