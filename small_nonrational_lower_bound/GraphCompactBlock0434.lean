module
prelude
import GraphInputsRow29Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0434
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 40074576256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record000_result⟩)
 (.leaf ⟨(29, 44633768320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 47824585088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 109798719872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record003_result⟩)
 (.leaf ⟨(29, 109937000704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 112228123008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 114229870848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record006_result⟩)
 (.leaf ⟨(29, 116647886880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 122815611136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 123090337920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record009_result⟩)
 (.leaf ⟨(29, 156033433920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 156034474304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record011_result⟩)
 (.leaf ⟨(29, 191809814592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 624192225536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 624661987360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record014_result⟩)
 (.leaf ⟨(29, 628485095680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(29, 628749336832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 628822736928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record017_result⟩)
 (.leaf ⟨(29, 660095402240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(29, 663987749120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record019_result⟩)
 (.branch 21
 (.leaf ⟨(29, 664256151808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record020_result⟩)
 (.leaf ⟨(29, 664256217088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(29, 696347304256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record022_result⟩)
 (.leaf ⟨(29, 705861615648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record023_result⟩))
 (.branch 25
 (.leaf ⟨(29, 706058699008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record024_result⟩)
 (.branch 26
 (.leaf ⟨(29, 706062942336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record025_result⟩)
 (.leaf ⟨(29, 706065039424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(29, 732973531392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record027_result⟩)
 (.branch 29
 (.leaf ⟨(29, 735053906176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record028_result⟩)
 (.leaf ⟨(29, 739298607232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(29, 741295095808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record030_result⟩)
 (.branch 32
 (.leaf ⟨(29, 797525999872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record031_result⟩)
 (.leaf ⟨(29, 797534388224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(29, 801686749440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record033_result⟩)
 (.branch 35
 (.leaf ⟨(29, 801695137792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record034_result⟩)
 (.leaf ⟨(29, 805583257856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(29, 806120128512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record036_result⟩)
 (.branch 38
 (.leaf ⟨(29, 810408771840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record037_result⟩)
 (.leaf ⟨(29, 814168998144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(29, 814705868800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record039_result⟩)
 (.branch 41
 (.leaf ⟨(29, 814714191872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_result⟩)
 (.leaf ⟨(29, 818329747712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(29, 818602377216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record042_result⟩)
 (.branch 44
 (.leaf ⟨(29, 818866618368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record043_result⟩)
 (.leaf ⟨(29, 818874941440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20446 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 20446 20491 :=
  block_of_table results 20446 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0434
