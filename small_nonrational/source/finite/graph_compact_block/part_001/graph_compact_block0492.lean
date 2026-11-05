module
prelude
import GraphInputsRow29Part00058Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0492
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 10896617243392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 10896889937920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record001_result⟩)
 (.leaf ⟨(29, 10896898260992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 10897137664000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record003_result⟩)
 (.leaf ⟨(29, 10901191131136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 10901298413568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record005_result⟩)
 (.leaf ⟨(29, 10905735659520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(29, 10909235839232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 10909619912704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record008_result⟩)
 (.leaf ⟨(29, 10909772709888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 10909776871424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record010_result⟩)
 (.leaf ⟨(29, 10909888315392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 10913512063232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record012_result⟩)
 (.leaf ⟨(29, 10914317206016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21320 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 21320 21334 :=
  block_of_table results 21320 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0492
