module
prelude
import GraphInputsRow28Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0428
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 25658203832320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 25703368163328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record001_result⟩)
 (.leaf ⟨(28, 25739881611264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 25757053091840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 25772093865984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record004_result⟩)
 (.leaf ⟨(28, 25776783097856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 25789265346560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 25917451665408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record007_result⟩)
 (.leaf ⟨(28, 25925773164544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(28, 25926301646848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record009_result⟩)
 (.leaf ⟨(28, 25933054476288), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record010_result⟩))
 (.branch 12
 (.leaf ⟨(28, 25977178619904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record011_result⟩)
 (.leaf ⟨(28, 25994358423552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(28, 25994886905856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record013_result⟩)
 (.branch 15
 (.leaf ⟨(28, 25997478985728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record014_result⟩)
 (.leaf ⟨(28, 26114613379072), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(28, 26126328004608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record016_result⟩)
 (.leaf ⟨(28, 26132057423872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record017_result⟩))
 (.branch 19
 (.leaf ⟨(28, 26139206615040), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record018_result⟩)
 (.leaf ⟨(28, 26207890571264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(28, 26250859053056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record020_result⟩)
 (.branch 22
 (.leaf ⟨(28, 26319584755712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record021_result⟩)
 (.leaf ⟨(28, 26336756236288), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(28, 26391807541504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record023_result⟩)
 (.leaf ⟨(28, 26392080171136), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record024_result⟩))
 (.branch 26
 (.leaf ⟨(28, 26428349415424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record025_result⟩)
 (.leaf ⟨(28, 26432919060480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record026_result⟩))))))
 (.branch 41
 (.branch 34
 (.branch 30
 (.branch 28
 (.leaf ⟨(28, 26462708105216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record027_result⟩)
 (.branch 29
 (.leaf ⟨(28, 26466868854784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record028_result⟩)
 (.leaf ⟨(28, 26467065929984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(28, 26498610298880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record030_result⟩)
 (.leaf ⟨(28, 26498618621952), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record031_result⟩))
 (.branch 33
 (.leaf ⟨(28, 26502779371520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record032_result⟩)
 (.leaf ⟨(28, 26511100870656), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record033_result⟩))))
 (.branch 37
 (.branch 35
 (.leaf ⟨(28, 26511493070848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 26513639505920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record035_result⟩)
 (.leaf ⟨(28, 26535995129856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(28, 26537035317248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record037_result⟩)
 (.leaf ⟨(28, 26571360583680), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record038_result⟩))
 (.branch 40
 (.leaf ⟨(28, 26571622645760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record039_result⟩)
 (.leaf ⟨(28, 26616718696448), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record040_result⟩)))))
 (.branch 48
 (.branch 44
 (.branch 42
 (.leaf ⟨(28, 26716980412544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record041_result⟩)
 (.branch 43
 (.leaf ⟨(28, 26717248847872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record042_result⟩)
 (.leaf ⟨(28, 26717253009408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(28, 26757714428032), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record044_result⟩)
 (.leaf ⟨(28, 27016753578752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record045_result⟩))
 (.branch 47
 (.leaf ⟨(28, 27016762032128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record046_result⟩)
 (.leaf ⟨(28, 27017026273280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record047_result⟩))))
 (.branch 51
 (.branch 49
 (.leaf ⟨(28, 27017034596352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record048_result⟩)
 (.branch 50
 (.leaf ⟨(28, 27017224454144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record049_result⟩)
 (.leaf ⟨(28, 27025616175104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record050_result⟩)))
 (.branch 53
 (.branch 52
 (.leaf ⟨(28, 27025814355968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record051_result⟩)
 (.leaf ⟨(28, 27033329999872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record052_result⟩))
 (.branch 54
 (.leaf ⟨(28, 27080054546688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record053_result⟩)
 (.leaf ⟨(28, 27094333554688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00008.record054_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20101 + i))) 0 55 :=
  interval_of_check _ 0 55 (by decide +kernel)

public theorem complete : Block 20101 20156 :=
  block_of_table results 20101 55 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0428
