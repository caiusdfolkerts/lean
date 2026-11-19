module
prelude
import GraphInputsRow26Part00051Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0367
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 33
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 25194815162432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record000_result⟩)
 (.leaf ⟨(26, 25215752995332), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 25215753126912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record002_result⟩)
 (.leaf ⟨(26, 25222350700544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 25261126975488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record004_result⟩)
 (.leaf ⟨(26, 25261655457792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 25292167020544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record006_result⟩)
 (.leaf ⟨(26, 25292401807616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 25292565397760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record008_result⟩)
 (.leaf ⟨(26, 25292565463040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 25292571689024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record010_result⟩)
 (.leaf ⟨(26, 25292672340032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 25294313390336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record012_result⟩)
 (.leaf ⟨(26, 25294313455616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 25294447591680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record014_result⟩)
 (.leaf ⟨(26, 25294447656960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 25294709817344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record016_result⟩)
 (.leaf ⟨(26, 25294716059648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 25294746423552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record018_result⟩)
 (.leaf ⟨(26, 25294752714816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 25295893565456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record020_result⟩)
 (.leaf ⟨(26, 25299004702976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 25299004768256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record022_result⟩)
 (.leaf ⟨(26, 25299010994240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 25299012034624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record024_result⟩)
 (.leaf ⟨(26, 25307228672256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 25307234963520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record026_result⟩)
 (.leaf ⟨(26, 25307594670080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 25307596734528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record028_result⟩)
 (.leaf ⟨(26, 25307597774912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 25307631325248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 25308507934736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record031_result⟩)
 (.leaf ⟨(26, 25327716352000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record032_result⟩)))))))
 (.branch 49
 (.branch 41
 (.branch 37
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 25327732801792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record033_result⟩)
 (.leaf ⟨(26, 25327732867072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 25327982088448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record035_result⟩)
 (.leaf ⟨(26, 25327984754688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(26, 25327988379712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record037_result⟩)
 (.leaf ⟨(26, 25328105818128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record038_result⟩))
 (.branch 40
 (.leaf ⟨(26, 25328772923392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record039_result⟩)
 (.leaf ⟨(26, 25329041326080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record040_result⟩))))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf ⟨(26, 25329179557889), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record041_result⟩)
 (.leaf ⟨(26, 25332279689280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record042_result⟩))
 (.branch 44
 (.leaf ⟨(26, 25340720187408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record043_result⟩)
 (.leaf ⟨(26, 25340865429568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 25340866990144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record045_result⟩)
 (.leaf ⟨(26, 25341793927169), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 25359794340096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record047_result⟩)
 (.leaf ⟨(26, 25359794405376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record048_result⟩)))))
 (.branch 57
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf ⟨(26, 25359797981440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record049_result⟩)
 (.leaf ⟨(26, 25359930102016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record050_result⟩))
 (.branch 52
 (.leaf ⟨(26, 25362076082176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record051_result⟩)
 (.leaf ⟨(26, 25362076537088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record052_result⟩)))
 (.branch 55
 (.branch 54
 (.leaf ⟨(26, 25362344484864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record053_result⟩)
 (.leaf ⟨(26, 25362398447632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record054_result⟩))
 (.branch 56
 (.leaf ⟨(26, 25366639419456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record055_result⟩)
 (.leaf ⟨(26, 25366639435776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record056_result⟩))))
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf ⟨(26, 25366691317776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record057_result⟩)
 (.leaf ⟨(26, 25375225176064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record058_result⟩))
 (.branch 60
 (.leaf ⟨(26, 25375954436097), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record059_result⟩)
 (.leaf ⟨(26, 25376350797825), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record060_result⟩)))
 (.branch 63
 (.branch 62
 (.leaf ⟨(26, 25384901951488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record061_result⟩)
 (.leaf ⟨(26, 25398964453376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record062_result⟩))
 (.branch 64
 (.leaf ⟨(26, 25428515361024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record063_result⟩)
 (.branch 65
 (.leaf ⟨(26, 25428918014016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record064_result⟩)
 (.leaf ⟨(26, 25431058157824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00051.record065_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16640 + i))) 0 66 :=
  interval_of_check _ 0 66 (by decide +kernel)

public theorem complete : Block 16640 16706 :=
  block_of_table results 16640 66 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0367
