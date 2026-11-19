module
prelude
import GraphInputsRow26Part00065Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0381
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 31042488500224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record000_result⟩)
 (.leaf ⟨(26, 31046781370368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 31050537435136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record002_result⟩)
 (.leaf ⟨(26, 31050809999360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 31051272421376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record004_result⟩)
 (.leaf ⟨(26, 31057513545728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 31064534827136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record006_result⟩)
 (.leaf ⟨(26, 31096730304640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 31098265944192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record008_result⟩)
 (.leaf ⟨(26, 31116031574144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 31175423885312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record010_result⟩)
 (.leaf ⟨(26, 31202208661504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 31235444326400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record012_result⟩)
 (.leaf ⟨(26, 31235485483264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 31239650213888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 31244343575104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record015_result⟩)
 (.leaf ⟨(26, 31260986720256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 31274149347328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record017_result⟩)
 (.leaf ⟨(26, 31337449357344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 31341764681984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record019_result⟩)
 (.leaf ⟨(26, 31344965521440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 31345229762592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record021_result⟩)
 (.leaf ⟨(26, 31376149643520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 31376158031872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record023_result⟩)
 (.leaf ⟨(26, 31376616227072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 31376627736576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record025_result⟩)
 (.leaf ⟨(26, 31380318781440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 31380450902016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record027_result⟩)
 (.leaf ⟨(26, 31380776976640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(26, 31380788486144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record029_result⟩)
 (.leaf ⟨(26, 31381862223872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record030_result⟩))
 (.branch 32
 (.leaf ⟨(26, 31389036642304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 31413685002240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record032_result⟩)
 (.leaf ⟨(26, 31413949243392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00065.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17183 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 17183 17217 :=
  block_of_table results 17183 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0381
