module
prelude
import GraphInputsRow29Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0447
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 3240963932160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record000_result⟩)
 (.leaf ⟨(29, 3241228173312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 3241236496384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record002_result⟩)
 (.leaf ⟨(29, 3243308548096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 3243316871168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record004_result⟩)
 (.leaf ⟨(29, 3249281204480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 3249818075136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 3249950195712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record007_result⟩)
 (.leaf ⟨(29, 3255654449408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 3338676502784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record009_result⟩)
 (.leaf ⟨(29, 3372969132288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 3377129881856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record011_result⟩)
 (.leaf ⟨(29, 3415174349056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(29, 3423764250880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record013_result⟩)
 (.leaf ⟨(29, 3423772639232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record014_result⟩))
 (.branch 16
 (.leaf ⟨(29, 3492490018816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 3524702273536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record016_result⟩)
 (.leaf ⟨(29, 3527447478272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20696 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 20696 20714 :=
  block_of_table results 20696 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0447
