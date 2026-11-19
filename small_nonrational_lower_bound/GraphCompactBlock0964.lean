module
prelude
import GraphInputsRow31Part00176Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0964
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 34713536299008), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record000_result⟩)
 (.leaf ⟨(31, 34729139109888), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 34772072595456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record002_result⟩)
 (.leaf ⟨(31, 34789252399104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 34790308970496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record004_result⟩)
 (.leaf ⟨(31, 34840799870976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 34909494315024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 35046933268480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record007_result⟩)
 (.leaf ⟨(31, 35115669389312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26796 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 26796 26805 :=
  block_of_table results 26796 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0964
