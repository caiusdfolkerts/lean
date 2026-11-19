module
prelude
import GraphInputsRow16Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0010
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 15590786875648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 15602888572928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record001_result⟩)
 (.leaf ⟨(16, 15614466916352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 15614936621056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 15615159443712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record004_result⟩)
 (.leaf ⟨(16, 15626371399680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 15626510802944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 15626635640832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record007_result⟩)
 (.leaf ⟨(16, 15626643963904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(16, 15627345526784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record009_result⟩)
 (.leaf ⟨(16, 15627411587072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record010_result⟩))
 (.branch 12
 (.leaf ⟨(16, 15627543707648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record011_result⟩)
 (.leaf ⟨(16, 15629491961856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(16, 15636124237824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record013_result⟩)
 (.branch 15
 (.leaf ⟨(16, 15638270672896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record014_result⟩)
 (.leaf ⟨(16, 15638324054272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(16, 15642484803840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record016_result⟩)
 (.leaf ⟨(16, 15649262797824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record017_result⟩))
 (.branch 19
 (.leaf ⟨(16, 15649518650112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record018_result⟩)
 (.leaf ⟨(16, 15661736853504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(16, 15661877167104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record020_result⟩)
 (.branch 22
 (.leaf ⟨(16, 15663817228288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record021_result⟩)
 (.leaf ⟨(16, 15820619055104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 15820685115392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record023_result⟩)
 (.leaf ⟨(16, 15820817235968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 15820824518656), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record025_result⟩)
 (.leaf ⟨(16, 15820915220736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record026_result⟩))))))
 (.branch 41
 (.branch 34
 (.branch 30
 (.branch 28
 (.leaf ⟨(16, 16094899216384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 16095156174848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record028_result⟩)
 (.leaf ⟨(16, 16095164497920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(16, 16127212126208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record030_result⟩)
 (.leaf ⟨(16, 16143037825024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record031_result⟩))
 (.branch 33
 (.leaf ⟨(16, 16174902476800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record032_result⟩)
 (.leaf ⟨(16, 16175992078336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record033_result⟩))))
 (.branch 37
 (.branch 35
 (.leaf ⟨(16, 16363998415104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record034_result⟩)
 (.branch 36
 (.leaf ⟨(16, 16401817403392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record035_result⟩)
 (.leaf ⟨(16, 16531617054976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(16, 16532744765696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record037_result⟩)
 (.leaf ⟨(16, 16532748927232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record038_result⟩))
 (.branch 40
 (.leaf ⟨(16, 16532748992512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record039_result⟩)
 (.leaf ⟨(16, 16570294493440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record040_result⟩)))))
 (.branch 48
 (.branch 44
 (.branch 42
 (.leaf ⟨(16, 16571370053888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record041_result⟩)
 (.branch 43
 (.leaf ⟨(16, 16575655641344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record042_result⟩)
 (.leaf ⟨(16, 16575924044032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(16, 16575935553536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record044_result⟩)
 (.leaf ⟨(16, 16576192512000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record045_result⟩))
 (.branch 47
 (.leaf ⟨(16, 16576200835072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record046_result⟩)
 (.leaf ⟨(16, 16588549922816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record047_result⟩))))
 (.branch 51
 (.branch 49
 (.leaf ⟨(16, 16591769575424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record048_result⟩)
 (.branch 50
 (.leaf ⟨(16, 16599381770496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record049_result⟩)
 (.leaf ⟨(16, 16599390158848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record050_result⟩)))
 (.branch 53
 (.branch 52
 (.leaf ⟨(16, 16605763403776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record051_result⟩)
 (.leaf ⟨(16, 16606023418112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record052_result⟩))
 (.branch 54
 (.leaf ⟨(16, 16606894293248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record053_result⟩)
 (.leaf ⟨(16, 16607162695936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00010.record054_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (768 + i))) 0 55 :=
  interval_of_check _ 0 55 (by decide +kernel)

public theorem complete : Block 768 823 :=
  block_of_table results 768 55 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0010
