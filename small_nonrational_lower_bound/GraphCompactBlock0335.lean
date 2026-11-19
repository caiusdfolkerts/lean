module
prelude
import GraphInputsRow26Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0335
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 12100304969984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record000_result⟩)
 (.leaf ⟨(26, 12100342743056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 12100572364928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 12104703754256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record003_result⟩)
 (.leaf ⟨(26, 12113223434256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 12113290534928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 12113455136896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record006_result⟩)
 (.leaf ⟨(26, 12133578407952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 12133842649104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 12133845221504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record009_result⟩)
 (.leaf ⟨(26, 12134901792896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 12138137600016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 12142287786240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record012_result⟩)
 (.leaf ⟨(26, 12146727501840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 12166054903824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 12167932354816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record015_result⟩)
 (.leaf ⟨(26, 12168204951680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 12172496289808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 12172497330192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record018_result⟩)
 (.leaf ⟨(26, 12172499902592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 12211007324160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 12234374299904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record021_result⟩)
 (.leaf ⟨(26, 12234374332544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 12234375921680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record023_result⟩)
 (.leaf ⟨(26, 12234510123024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 12236656558096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 12255186927744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record026_result⟩)
 (.leaf ⟨(26, 12327967588352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(26, 12371810680848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 12371944882192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record029_result⟩)
 (.leaf ⟨(26, 12372213284880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(26, 12374359719952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 12378652590096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record032_result⟩)
 (.leaf ⟨(26, 12384035946624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(26, 12392357445760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 12439587487744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record035_result⟩)
 (.leaf ⟨(26, 12439589568512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(26, 12439640869120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record037_result⟩)
 (.branch 39
 (.leaf ⟨(26, 12439645063296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record038_result⟩)
 (.leaf ⟨(26, 12439855857792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(26, 12439857938560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record040_result⟩)
 (.branch 42
 (.leaf ⟨(26, 12439857971200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record041_result⟩)
 (.leaf ⟨(26, 12464046489728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(26, 12465136091264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record043_result⟩)
 (.branch 45
 (.leaf ⟨(26, 12465138204672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record044_result⟩)
 (.leaf ⟨(26, 12465142236160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15051 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 15051 15097 :=
  block_of_table results 15051 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0335
