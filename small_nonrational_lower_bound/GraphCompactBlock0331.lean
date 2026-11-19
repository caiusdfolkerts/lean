module
prelude
import GraphInputsRow26Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0331
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 10122237576448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record000_result⟩)
 (.leaf ⟨(26, 10136215404800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 10138413137928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 10153378365448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record003_result⟩)
 (.leaf ⟨(26, 10156268077056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(26, 10164723777536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record005_result⟩)
 (.leaf ⟨(26, 10164847575040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record006_result⟩))
 (.branch 8
 (.leaf ⟨(26, 10206006264064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 10206072324352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record008_result⟩)
 (.leaf ⟨(26, 10209427218688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 10210425012224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record010_result⟩)
 (.leaf ⟨(26, 10211696410624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 10214717882368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 10226185043968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record013_result⟩)
 (.leaf ⟨(26, 10226189205504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(26, 10228265418752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record015_result⟩)
 (.leaf ⟨(26, 10228269580288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record016_result⟩))
 (.branch 18
 (.leaf ⟨(26, 10231897686016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 10232426168320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record018_result⟩)
 (.leaf ⟨(26, 10232430329856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 10267222114560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record020_result⟩)
 (.leaf ⟨(26, 10273650163968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 10301613441280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record022_result⟩)
 (.branch 24
 (.leaf ⟨(26, 10301617668096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record023_result⟩)
 (.leaf ⟨(26, 10301621829632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 10301625861120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record025_result⟩)
 (.leaf ⟨(26, 10301757981696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 10301881713408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 10302016077952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record028_result⟩)
 (.leaf ⟨(26, 10302022222848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(26, 10302150148736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record030_result⟩)
 (.leaf ⟨(26, 10345110308992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record031_result⟩))
 (.branch 33
 (.leaf ⟨(26, 10347190683776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 10349139001344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record033_result⟩)
 (.leaf ⟨(26, 10359672932480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(26, 10370603352064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 10372683726848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record036_result⟩)
 (.leaf ⟨(26, 10372692049920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(26, 10484292159760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 10708171358208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record039_result⟩)
 (.leaf ⟨(26, 10716757098496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00015.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14835 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 14835 14876 :=
  block_of_table results 14835 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0331
