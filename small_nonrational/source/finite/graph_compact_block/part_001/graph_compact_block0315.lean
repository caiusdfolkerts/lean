module
prelude
import GraphInputsRow25Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0315
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 34711943053312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record000_result⟩)
 (.leaf ⟨(25, 34712479858688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 34712999624704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record002_result⟩)
 (.leaf ⟨(25, 34729105690624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 34737716527104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record004_result⟩)
 (.leaf ⟨(25, 34739046055936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 34747896037376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record006_result⟩)
 (.leaf ⟨(25, 34763465424896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(25, 34763498848256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record008_result⟩)
 (.leaf ⟨(25, 34789235230736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record009_result⟩))
 (.branch 11
 (.leaf ⟨(25, 34790308839940), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record010_result⟩)
 (.leaf ⟨(25, 34840774838528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(25, 34875159609344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record012_result⟩)
 (.leaf ⟨(25, 34892331089920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record013_result⟩))
 (.branch 15
 (.leaf ⟨(25, 35115652745216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record014_result⟩)
 (.branch 16
 (.leaf ⟨(25, 35115669651456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record015_result⟩)
 (.leaf ⟨(25, 35150029127680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13999 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 13999 14016 :=
  block_of_table results 13999 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0315
