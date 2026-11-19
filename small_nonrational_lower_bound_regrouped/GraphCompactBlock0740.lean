module
prelude
import GraphInputsRow30Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0740
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 7003355217920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record000_result⟩)
 (.leaf ⟨(30, 7003619459072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 7003883700224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 7048242954496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record003_result⟩)
 (.leaf ⟨(30, 7050864164864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 7098039566336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record005_result⟩)
 (.leaf ⟨(30, 7150227194112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 7150227259392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 7150359379968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record008_result⟩)
 (.leaf ⟨(30, 7150462046464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 7154085924880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record010_result⟩)
 (.leaf ⟨(30, 7156800765952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 7156901351680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 7157062926336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record013_result⟩)
 (.leaf ⟨(30, 7157065007104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(30, 7158246674448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record015_result⟩)
 (.leaf ⟨(30, 7165421031680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record016_result⟩))
 (.branch 18
 (.leaf ⟨(30, 7185774510080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 7185778086144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record018_result⟩)
 (.leaf ⟨(30, 7186298177552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23951 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 23951 23971 :=
  block_of_table results 23951 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0740
