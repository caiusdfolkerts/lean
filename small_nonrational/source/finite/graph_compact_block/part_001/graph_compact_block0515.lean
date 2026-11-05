module
prelude
import GraphInputsRow29Part00081Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0515
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 13204378959904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record000_result⟩)
 (.leaf ⟨(29, 13233084244224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 13233088462880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 13234484576512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record003_result⟩)
 (.leaf ⟨(29, 13234484641792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 13237377114368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record005_result⟩)
 (.leaf ⟨(29, 13237645517056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 13237645574176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 13237647654944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record008_result⟩)
 (.leaf ⟨(29, 13238777446656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 13238777511936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record010_result⟩)
 (.leaf ⟨(29, 13247168127232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 13247363186944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 13247363252224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record013_result⟩)
 (.leaf ⟨(29, 13247367381120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(29, 13247436562560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 13271743143968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record016_result⟩)
 (.leaf ⟨(29, 13272007385120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(29, 13273136201728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 13273139257600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record019_result⟩)
 (.leaf ⟨(29, 13274176389120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00081.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21599 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 21599 21620 :=
  block_of_table results 21599 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0515
