module
prelude
import GraphInputsRow29Part00181Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0615
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 26426541637760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 26427089527040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record001_result⟩)
 (.leaf ⟨(29, 26427221647616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 26428221521920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 26428353577216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record004_result⟩)
 (.leaf ⟨(29, 26428353642496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 26428617883648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 26428622012544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record007_result⟩)
 (.leaf ⟨(29, 26428624093312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 26428691193984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 26431522938944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record010_result⟩)
 (.leaf ⟨(29, 26431539454016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(29, 26432984064128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 26441305563264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record013_result⟩)
 (.leaf ⟨(29, 26462712332288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(29, 26462715388160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 26462980702336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record016_result⟩)
 (.leaf ⟨(29, 26462983823488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(29, 26463185149984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 26463785549824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record019_result⟩)
 (.leaf ⟨(29, 26464020889728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(29, 26464024010880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_result⟩)
 (.leaf ⟨(29, 26464258887712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record022_result⟩))
 (.branch 24
 (.leaf ⟨(29, 26466873016576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record023_result⟩)
 (.leaf ⟨(29, 26466873081856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22840 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 22840 22865 :=
  block_of_table results 22840 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0615
