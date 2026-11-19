module
prelude
import GraphInputsRow26Part00057Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0373
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 27682475671552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 27682483994624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record001_result⟩)
 (.leaf ⟨(26, 27686502154496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 27686636421120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 27686644744192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record004_result⟩)
 (.leaf ⟨(26, 27687039025152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 27687105085440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 27689688776960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record007_result⟩)
 (.leaf ⟨(26, 27689756983296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 27689765306368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 27690225647616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record010_result⟩)
 (.leaf ⟨(26, 27721969238016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 27721977561088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 27730752110592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record013_result⟩)
 (.leaf ⟨(26, 27731022594048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 27731127730432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 27731140020224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record016_result⟩)
 (.leaf ⟨(26, 27735426662400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 27737461899264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 27756360564736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record019_result⟩)
 (.leaf ⟨(26, 27756368887808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(26, 27756763168768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 27756897239552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record022_result⟩)
 (.leaf ⟨(26, 27783240646656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00057.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16913 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 16913 16937 :=
  block_of_table results 16913 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0373
