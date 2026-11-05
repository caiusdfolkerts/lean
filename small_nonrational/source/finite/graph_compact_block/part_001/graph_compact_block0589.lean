module
prelude
import GraphInputsRow29Part00155Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0589
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24786294079744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record000_result⟩)
 (.leaf ⟨(29, 24787062161408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24791222587520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record002_result⟩)
 (.leaf ⟨(29, 24799947014144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 24825515217024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record004_result⟩)
 (.leaf ⟨(29, 24826588693120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 24855252631552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 24883698925568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record007_result⟩)
 (.leaf ⟨(29, 24886720397312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 24886728720384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record009_result⟩)
 (.leaf ⟨(29, 24889940049920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 24894773428480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record011_result⟩)
 (.leaf ⟨(29, 24894909775872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(29, 24894918098944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record013_result⟩)
 (.leaf ⟨(29, 24895041896448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record014_result⟩))
 (.branch 16
 (.leaf ⟨(29, 24895050219520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 24895510560768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record016_result⟩)
 (.leaf ⟨(29, 24895813615872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22637 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 22637 22655 :=
  block_of_table results 22637 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0589
