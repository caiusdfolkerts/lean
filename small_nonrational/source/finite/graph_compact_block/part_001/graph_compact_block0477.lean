module
prelude
import GraphInputsRow29Part00043Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0477
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 7611353432064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record000_result⟩)
 (.leaf ⟨(29, 7614977179904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7615782322688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 7619410460672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record003_result⟩)
 (.leaf ⟨(29, 7620079386624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 7623566950916), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record005_result⟩)
 (.leaf ⟨(29, 7623567082496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 7623567147008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 7623843774464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record008_result⟩)
 (.leaf ⟨(29, 7624103952384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 7699980910848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record010_result⟩)
 (.leaf ⟨(29, 7702127345920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 7702523707648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 7735412556032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record013_result⟩)
 (.leaf ⟨(29, 7736985190656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 7749876350976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record015_result⟩)
 (.leaf ⟨(29, 7753087615232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 7784168980480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record017_result⟩)
 (.branch 19
 (.leaf ⟨(29, 7785299869952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record018_result⟩)
 (.leaf ⟨(29, 7821945012224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00043.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21069 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 21069 21089 :=
  block_of_table results 21069 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0477
