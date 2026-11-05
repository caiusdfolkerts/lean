module
prelude
import GraphInputsRow30Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0756
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 14311387336736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record000_result⟩)
 (.leaf ⟨(30, 14372579778560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 14448834121760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 14449958191105), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record003_result⟩)
 (.leaf ⟨(30, 14449960304640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 14450027405312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record005_result⟩)
 (.leaf ⟨(30, 14453370790144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 14571853086976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 14588460941440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record008_result⟩)
 (.leaf ⟨(30, 14604048564480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 14604052791296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record010_result⟩)
 (.leaf ⟨(30, 14616457379840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 14621748527104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 14623428378624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record013_result⟩)
 (.leaf ⟨(30, 14623700942848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(30, 14623965184000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record015_result⟩)
 (.leaf ⟨(30, 14759793590272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record016_result⟩))
 (.branch 18
 (.leaf ⟨(30, 14760462516224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 14768387653632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record018_result⟩)
 (.leaf ⟨(30, 14768916135936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 15037494198272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record020_result⟩)
 (.leaf ⟨(30, 15212845531136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 15213580517376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record022_result⟩)
 (.branch 24
 (.leaf ⟨(30, 15247410724864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record023_result⟩)
 (.leaf ⟨(30, 15311835234304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(30, 15326867685376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record025_result⟩)
 (.leaf ⟨(30, 15335725989888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record026_result⟩))
 (.branch 28
 (.leaf ⟨(30, 15344047489024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 15350288613376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record028_result⟩)
 (.leaf ⟨(30, 15399114514560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(30, 15411993124992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record030_result⟩)
 (.leaf ⟨(30, 15471034769536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record031_result⟩))
 (.branch 33
 (.leaf ⟨(30, 15576506368000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 15672633462816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record033_result⟩)
 (.leaf ⟨(30, 15677190574112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(30, 15679382634624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record035_result⟩)
 (.branch 37
 (.leaf ⟨(30, 15712410140672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record036_result⟩)
 (.leaf ⟨(30, 15712670220288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(30, 15723208376320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record038_result⟩)
 (.branch 40
 (.leaf ⟨(30, 15809306984448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record039_result⟩)
 (.leaf ⟨(30, 15842282569728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00028.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24421 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 24421 24462 :=
  block_of_table results 24421 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0756
