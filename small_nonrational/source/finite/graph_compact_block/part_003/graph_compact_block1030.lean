module
prelude
import GraphInputsSix0Part00065Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1030
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 24640513655040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record000_result⟩)
 (.leaf ⟨(32, 24640515801088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 24640522043392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record002_result⟩)
 (.branch 4
 (.leaf ⟨(32, 24640563200256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record003_result⟩)
 (.leaf ⟨(32, 24640573409280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(32, 24640837650432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record005_result⟩)
 (.branch 7
 (.leaf ⟨(32, 24641032953920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record006_result⟩)
 (.leaf ⟨(32, 24642777514752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(32, 24643180167744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record008_result⟩)
 (.branch 10
 (.leaf ⟨(32, 24644723949824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record009_result⟩)
 (.leaf ⟨(32, 24644734158848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(32, 24645077057600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record011_result⟩)
 (.branch 13
 (.leaf ⟨(32, 24645079154688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record012_result⟩)
 (.leaf ⟨(32, 24645126602816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(32, 24645193703488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record014_result⟩)
 (.branch 16
 (.leaf ⟨(32, 24647340917312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record015_result⟩)
 (.leaf ⟨(32, 24655662416448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(32, 24663849844800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record017_result⟩)
 (.branch 19
 (.leaf ⟨(32, 24663984062464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record018_result⟩)
 (.leaf ⟨(32, 24663986143232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(32, 24665997320256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record020_result⟩)
 (.branch 22
 (.leaf ⟨(32, 24666064437248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record021_result⟩)
 (.leaf ⟨(32, 24666066518016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record022_result⟩))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf ⟨(32, 24666198508032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record023_result⟩)
 (.branch 25
 (.leaf ⟨(32, 24672525648128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record024_result⟩)
 (.leaf ⟨(32, 24672536117248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record025_result⟩)))
 (.branch 27
 (.leaf ⟨(32, 24672734298112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record026_result⟩)
 (.branch 28
 (.leaf ⟨(32, 24672775454976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record027_result⟩)
 (.leaf ⟨(32, 24676940185600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record028_result⟩))))
 (.branch 32
 (.branch 30
 (.leaf ⟨(32, 24681633546816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record029_result⟩)
 (.branch 31
 (.leaf ⟨(32, 24739062768000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record030_result⟩)
 (.leaf ⟨(32, 24739063288192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record031_result⟩)))
 (.branch 33
 (.leaf ⟨(32, 24739097907472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record032_result⟩)
 (.branch 34
 (.leaf ⟨(32, 24740136764288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record033_result⟩)
 (.leaf ⟨(32, 24740145217664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record034_result⟩)))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf ⟨(32, 24740154738960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record035_result⟩)
 (.branch 37
 (.leaf ⟨(32, 24740178247808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record036_result⟩)
 (.leaf ⟨(32, 24740245348480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(32, 24740647952512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record038_result⟩)
 (.branch 40
 (.leaf ⟨(32, 24741319086208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record039_result⟩)
 (.leaf ⟨(32, 24741335601280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record040_result⟩))))
 (.branch 44
 (.branch 42
 (.leaf ⟨(32, 24742409077376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record041_result⟩)
 (.branch 43
 (.leaf ⟨(32, 24742413238528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record042_result⟩)
 (.leaf ⟨(32, 24742413303808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record043_result⟩)))
 (.branch 45
 (.leaf ⟨(32, 24742541197568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record044_result⟩)
 (.branch 46
 (.leaf ⟨(32, 24742545359104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record045_result⟩)
 (.leaf ⟨(32, 24742545424384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00065.record046_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33192 + i))) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

public theorem complete : Block 33192 33239 :=
  block_of_table results 33192 47 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1030
