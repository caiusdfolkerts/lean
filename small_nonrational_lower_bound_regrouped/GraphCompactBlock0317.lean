module
prelude
import GraphInputsRow26Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0317
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 752030916608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 776661401856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record001_result⟩)
 (.leaf ⟨(26, 792717263104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 793105235976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 799422890240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record004_result⟩)
 (.leaf ⟨(26, 799478480904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 805583388928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 814173290752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record007_result⟩)
 (.leaf ⟨(26, 814173356032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 814177322240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 814714191873), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record010_result⟩)
 (.leaf ⟨(26, 818329878784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 818334040320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 818334105600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record013_result⟩)
 (.leaf ⟨(26, 818338071808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 818736709632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 818874941441), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_result⟩)
 (.leaf ⟨(26, 819130794752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 819139183104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 865744290048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record019_result⟩)
 (.leaf ⟨(26, 868999053568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 869267456256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record021_result⟩)
 (.leaf ⟨(26, 873298231296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 873830875136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record023_result⟩)
 (.leaf ⟨(26, 874871062528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record024_result⟩))))))
 (.branch 38
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(26, 930152022272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 936861810944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record026_result⟩)
 (.leaf ⟨(26, 939134124032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(26, 947858194560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 955904951552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record029_result⟩)
 (.leaf ⟨(26, 956305539328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(26, 956313927680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 956574007296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record032_result⟩)
 (.leaf ⟨(26, 956582330368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record033_result⟩)))
 (.branch 36
 (.branch 35
 (.leaf ⟨(26, 967782252800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record034_result⟩)
 (.leaf ⟨(26, 977212080384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record035_result⟩))
 (.branch 37
 (.leaf ⟨(26, 977216241920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record036_result⟩)
 (.leaf ⟨(26, 977216307200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record037_result⟩)))))
 (.branch 44
 (.branch 41
 (.branch 39
 (.leaf ⟨(26, 977315397632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 998993133576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record039_result⟩)
 (.leaf ⟨(26, 999139885312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(26, 1001015836928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record041_result⟩)
 (.branch 43
 (.leaf ⟨(26, 1001017917696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record042_result⟩)
 (.leaf ⟨(26, 1001073508360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record043_result⟩))))
 (.branch 47
 (.branch 45
 (.leaf ⟨(26, 1001286320384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record044_result⟩)
 (.branch 46
 (.leaf ⟨(26, 1009931878400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record045_result⟩)
 (.leaf ⟨(26, 1025031307264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(26, 1026566553856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record047_result⟩)
 (.leaf ⟨(26, 1026570585344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record048_result⟩))
 (.branch 50
 (.leaf ⟨(26, 1026711093249), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record049_result⟩)
 (.leaf ⟨(26, 1026843213825), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record050_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14068 + i))) 0 51 :=
  interval_of_check _ 0 51 (by decide +kernel)

public theorem complete : Block 14068 14119 :=
  block_of_table results 14068 51 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0317
