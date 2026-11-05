module
prelude
import GraphInputsRow23Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0104
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 31789477265408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record000_result⟩)
 (.leaf ⟨(23, 31790005747712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 31795718389760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record002_result⟩)
 (.leaf ⟨(23, 31812889870336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 31819336581120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record004_result⟩)
 (.leaf ⟨(23, 31827930644480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 31828459126784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record006_result⟩)
 (.leaf ⟨(23, 31842955689984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(23, 31891777421568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record008_result⟩)
 (.leaf ⟨(23, 31891788931072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record009_result⟩))
 (.branch 11
 (.leaf ⟨(23, 31896072372480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record010_result⟩)
 (.leaf ⟨(23, 31896081801216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(23, 31924225638400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record012_result⟩)
 (.leaf ⟨(23, 31930466762752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record013_result⟩))
 (.branch 15
 (.leaf ⟨(23, 31938788261888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record014_result⟩)
 (.leaf ⟨(23, 31939559981312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(23, 31940330143744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record016_result⟩)
 (.leaf ⟨(23, 31960731811840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record017_result⟩))
 (.branch 19
 (.leaf ⟨(23, 31963709186048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_result⟩)
 (.leaf ⟨(23, 31972294926336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(23, 31995635761152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record020_result⟩)
 (.leaf ⟨(23, 32010462625792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record021_result⟩))
 (.branch 23
 (.leaf ⟨(23, 32041010208832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record022_result⟩)
 (.leaf ⟨(23, 32041127383072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(23, 32042133750336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record024_result⟩)
 (.leaf ⟨(23, 32043208032256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record025_result⟩))
 (.branch 27
 (.leaf ⟨(23, 32060999794688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record026_result⟩)
 (.leaf ⟨(23, 32076495585280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(23, 32078179598336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_result⟩)
 (.leaf ⟨(23, 32078708080640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record029_result⟩))
 (.branch 31
 (.leaf ⟨(23, 32165295825152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record030_result⟩)
 (.leaf ⟨(23, 32169859227712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record031_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7587 + i))) 0 32 :=
  interval_of_check _ 0 32 (by decide +kernel)

public theorem complete : Block 7587 7619 :=
  block_of_table results 7587 32 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0104
