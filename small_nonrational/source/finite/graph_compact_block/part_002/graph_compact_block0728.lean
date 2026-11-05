module
prelude
import GraphInputsRow30Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0728
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 37994201472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record000_result⟩)
 (.leaf ⟨(30, 40074576256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 44633768320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record002_result⟩)
 (.leaf ⟨(30, 47824585088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 109798719872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record004_result⟩)
 (.leaf ⟨(30, 109937000704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 111963881856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record006_result⟩)
 (.leaf ⟨(30, 112228123008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 114229870848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record008_result⟩)
 (.leaf ⟨(30, 116647886880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 122815611136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record010_result⟩)
 (.leaf ⟨(30, 123090337920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 147447693632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record012_result⟩)
 (.leaf ⟨(30, 156033433920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 156034474304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 191809814592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record015_result⟩)
 (.leaf ⟨(30, 624192225536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record016_result⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(30, 624661987360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record017_result⟩)
 (.leaf ⟨(30, 628485095680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record018_result⟩))
 (.branch 20
 (.leaf ⟨(30, 628822736928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record019_result⟩)
 (.leaf ⟨(30, 660095402240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 661701986688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record021_result⟩)
 (.leaf ⟨(30, 663987749120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 664256151808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record023_result⟩)
 (.branch 25
 (.leaf ⟨(30, 664256217088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record024_result⟩)
 (.leaf ⟨(30, 696347304256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record025_result⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨(30, 697403875648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record026_result⟩)
 (.leaf ⟨(30, 706058699008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record027_result⟩))
 (.branch 29
 (.leaf ⟨(30, 706065039424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record028_result⟩)
 (.leaf ⟨(30, 732973531392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(30, 735053906176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record030_result⟩)
 (.leaf ⟨(30, 741295095808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record031_result⟩))
 (.branch 33
 (.leaf ⟨(30, 797525999872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 797534388224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record033_result⟩)
 (.leaf ⟨(30, 801686749440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00000.record034_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23554 + i))) 0 35 :=
  interval_of_check _ 0 35 (by decide +kernel)

public theorem complete : Block 23554 23589 :=
  block_of_table results 23554 35 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0728
