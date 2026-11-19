module
prelude
import GraphInputsRow26Part00083Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0399
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 34634667426048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 34634667491328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record001_result⟩)
 (.leaf ⟨(26, 34634671067392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 34634671132672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 34634910142480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record004_result⟩)
 (.leaf ⟨(26, 34634910402576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 34635841569024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 34635845795840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record007_result⟩)
 (.leaf ⟨(26, 34635853598720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 34635984142337), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 34637873185024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record010_result⟩)
 (.leaf ⟨(26, 34638009532416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 34638017855488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 34638240743424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_result⟩)
 (.leaf ⟨(26, 34639196983552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 34639205371904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 34639213498624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record016_result⟩)
 (.leaf ⟨(26, 34639716814864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 34640286974720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 34640790290960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_result⟩)
 (.leaf ⟨(26, 34641092837632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(26, 34641864560640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 34643248285712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record022_result⟩)
 (.leaf ⟨(26, 34670085439744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17611 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 17611 17635 :=
  block_of_table results 17611 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0399
