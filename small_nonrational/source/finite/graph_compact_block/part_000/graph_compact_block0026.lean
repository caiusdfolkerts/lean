module
prelude
import GraphInputsRow16Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0026
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 25963882876928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 25964419678208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record001_result⟩)
 (.leaf ⟨(16, 25964428001280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 25964956353024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 26118971752704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record004_result⟩)
 (.leaf ⟨(16, 26121089384448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 26152223932672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 26183396000000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record007_result⟩)
 (.leaf ⟨(16, 26184419672320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(16, 26184436187392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record009_result⟩)
 (.branch 11
 (.leaf ⟨(16, 26186516562176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record010_result⟩)
 (.leaf ⟨(16, 26188848889856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(16, 26502706020608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 26504048214016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record013_result⟩)
 (.leaf ⟨(16, 26574918270976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(16, 26575958458368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 26580954972160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record016_result⟩)
 (.leaf ⟨(16, 26644435730688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(16, 26644439957504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 26644778582016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record019_result⟩)
 (.leaf ⟨(16, 26648533541120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(16, 26652761456640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 26711816159488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record022_result⟩)
 (.leaf ⟨(16, 26712856346880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(16, 26777382560000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record024_result⟩)
 (.branch 26
 (.leaf ⟨(16, 26990990115072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record025_result⟩)
 (.leaf ⟨(16, 27016763064576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(16, 27025348804864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 27051119673600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record028_result⟩)
 (.leaf ⟨(16, 27053332168960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(16, 27053340557312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 27055412543744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record031_result⟩)
 (.leaf ⟨(16, 27055420932096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(16, 27068299542528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record033_result⟩)
 (.branch 35
 (.leaf ⟨(16, 27071486164992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record034_result⟩)
 (.leaf ⟨(16, 27087928885248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(16, 27113463808256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 27115544183040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record037_result⟩)
 (.leaf ⟨(16, 27115617526016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(16, 27123997802752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record039_result⟩)
 (.branch 41
 (.leaf ⟨(16, 27124006191104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record040_result⟩)
 (.leaf ⟨(16, 27124195983616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(16, 27124270432256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record042_result⟩)
 (.branch 44
 (.leaf ⟨(16, 27124398326016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record043_result⟩)
 (.leaf ⟨(16, 27124402552832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(16, 27124464386304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record045_result⟩)
 (.leaf ⟨(16, 27124475895808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record046_result⟩))
 (.branch 48
 (.leaf ⟨(16, 27124732854272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record047_result⟩)
 (.leaf ⟨(16, 27124741177344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00026.record048_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1530 + i))) 0 49 :=
  interval_of_check _ 0 49 (by decide +kernel)

public theorem complete : Block 1530 1579 :=
  block_of_table results 1530 49 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0026
