module
prelude
import GraphInputsRow24Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0145
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 15341641040128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record000_result⟩)
 (.leaf ⟨(24, 15341959053312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 15342182072320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record002_result⟩)
 (.leaf ⟨(24, 15342428758016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 15343770829056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record004_result⟩)
 (.leaf ⟨(24, 15344575971840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 15350213255424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 15507394723840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record007_result⟩)
 (.leaf ⟨(24, 15575241736192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 15592142733312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record009_result⟩)
 (.leaf ⟨(24, 15645102047232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 15647372279808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 15649527037952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record012_result⟩)
 (.leaf ⟨(24, 15662009286656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 15664089661440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record014_result⟩)
 (.leaf ⟨(24, 15671573364864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 15679954649344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 15679963037696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record017_result⟩)
 (.leaf ⟨(24, 15688544583808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 15703564451840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record019_result⟩)
 (.leaf ⟨(24, 15703570661504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 15703764713472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 15704033083520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record022_result⟩)
 (.leaf ⟨(24, 15729311236224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 15729317381120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record024_result⟩)
 (.leaf ⟨(24, 15806646730880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 15808182370432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 15839927812096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record027_result⟩)
 (.leaf ⟨(24, 15839931940992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(24, 15839931973632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record029_result⟩)
 (.leaf ⟨(24, 15842125416704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record030_result⟩))
 (.branch 32
 (.leaf ⟨(24, 15842129610880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 15848765145344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record032_result⟩)
 (.leaf ⟨(24, 15853128056832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(24, 15885340311552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record034_result⟩)
 (.leaf ⟨(24, 15987357319168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record035_result⟩))
 (.branch 37
 (.leaf ⟨(24, 16021649948672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 16128407503616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record037_result⟩)
 (.leaf ⟨(24, 16159357272064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00029.record038_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9143 + i))) 0 39 :=
  interval_of_check _ 0 39 (by decide +kernel)

public theorem complete : Block 9143 9182 :=
  block_of_table results 9143 39 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0145
