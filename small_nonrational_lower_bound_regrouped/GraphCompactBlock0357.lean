module
prelude
import GraphInputsRow26Part00041Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0357
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 22866517035136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record000_result⟩)
 (.leaf ⟨(26, 22867827769344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 22869761491200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 22869769879552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record003_result⟩)
 (.leaf ⟨(26, 22870298198656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 22876407267328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 22876944072704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record006_result⟩)
 (.leaf ⟨(26, 22925205831680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 22929094017024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 22929366581248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record009_result⟩)
 (.leaf ⟨(26, 22930901762304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 22931636813824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 22937679757312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record012_result⟩)
 (.leaf ⟨(26, 22937688080384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 22948081631232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 22948354195456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record015_result⟩)
 (.leaf ⟨(26, 22948816617472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 22956132565248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 22956143034368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record018_result⟩)
 (.leaf ⟨(26, 22962582339584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 22970903838720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 22980325343232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record021_result⟩)
 (.leaf ⟨(26, 22989099827456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record022_result⟩))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf ⟨(26, 22989378699264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record023_result⟩)
 (.branch 25
 (.leaf ⟨(26, 22989618036992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record024_result⟩)
 (.leaf ⟨(26, 22995818004480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record025_result⟩)))
 (.branch 27
 (.leaf ⟨(26, 22995859161344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record026_result⟩)
 (.branch 28
 (.leaf ⟨(26, 23006797627968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record027_result⟩)
 (.leaf ⟨(26, 23014582403328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record028_result⟩))))
 (.branch 32
 (.branch 30
 (.leaf ⟨(26, 23014716669952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 23014724993024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record030_result⟩)
 (.leaf ⟨(26, 23015119273984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record031_result⟩)))
 (.branch 33
 (.leaf ⟨(26, 23015253344768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 23028075397120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record033_result⟩)
 (.leaf ⟨(26, 23108574593056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record034_result⟩)))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf ⟨(26, 23130087129344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 23130087194624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record036_result⟩)
 (.leaf ⟨(26, 23134382080256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(26, 23134382145536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 23137603293440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record039_result⟩)
 (.leaf ⟨(26, 23142569443328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record040_result⟩))))
 (.branch 44
 (.branch 42
 (.leaf ⟨(26, 23142769704960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record041_result⟩)
 (.branch 43
 (.leaf ⟨(26, 23142967820544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record042_result⟩)
 (.leaf ⟨(26, 23142974111808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record043_result⟩)))
 (.branch 45
 (.leaf ⟨(26, 23143041212480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record044_result⟩)
 (.branch 46
 (.leaf ⟨(26, 23163321286688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record045_result⟩)
 (.leaf ⟨(26, 23167616237600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00041.record046_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16200 + i))) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

public theorem complete : Block 16200 16247 :=
  block_of_table results 16200 47 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0357
