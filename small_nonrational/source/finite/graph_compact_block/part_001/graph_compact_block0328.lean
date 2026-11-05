module
prelude
import GraphInputsRow26Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0328
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 7560310587648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 7560310652928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record001_result⟩)
 (.leaf ⟨(26, 7560376647936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 7560376713216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record003_result⟩)
 (.leaf ⟨(26, 7560773074944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 7560830650496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record005_result⟩)
 (.leaf ⟨(26, 7563181572096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 7563731607552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record007_result⟩)
 (.leaf ⟨(26, 7563748837632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 7563992727552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record009_result⟩)
 (.leaf ⟨(26, 7563995848704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 7564017272960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record011_result⟩)
 (.leaf ⟨(26, 7565127712769), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 7576433461376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record013_result⟩)
 (.leaf ⟨(26, 7576878620672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(26, 7577744195584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 7586199896064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record016_result⟩)
 (.leaf ⟨(26, 7586323693568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 7586332016640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record018_result⟩)
 (.leaf ⟨(26, 7586792357888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 7586860498944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record020_result⟩)
 (.leaf ⟨(26, 7593521219840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 7593521283080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record022_result⟩)
 (.leaf ⟨(26, 7593640790024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 7593644951560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record024_result⟩)
 (.leaf ⟨(26, 7593661923328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 7594066315392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record026_result⟩)
 (.leaf ⟨(26, 7597801538568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 7598074104064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record028_result⟩)
 (.leaf ⟨(26, 7598074169344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 7598090813952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 7598342539392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record031_result⟩)
 (.leaf ⟨(26, 7598346601480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 7598363377665), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record033_result⟩)
 (.leaf ⟨(26, 7598615037952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 7602658361344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record035_result⟩)
 (.leaf ⟨(26, 7602775787520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(26, 7602897699072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record037_result⟩)
 (.leaf ⟨(26, 7607070752768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record038_result⟩))
 (.branch 40
 (.leaf ⟨(26, 7623567082752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record039_result⟩)
 (.leaf ⟨(26, 7623575471104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(26, 7623705427968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record041_result⟩)
 (.leaf ⟨(26, 7623835582464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record042_result⟩))
 (.branch 44
 (.leaf ⟨(26, 7623843905536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record043_result⟩)
 (.leaf ⟨(26, 7623977992192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record044_result⟩)))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 7624103821828), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record045_result⟩)
 (.leaf ⟨(26, 7635122257920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 7641553240064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record047_result⟩)
 (.leaf ⟨(26, 7647604506624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(26, 7657998057472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record049_result⟩)
 (.leaf ⟨(26, 7658270621696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record050_result⟩))
 (.branch 52
 (.leaf ⟨(26, 7658733043712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record051_result⟩)
 (.leaf ⟨(26, 7700383613056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record052_result⟩))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf ⟨(26, 7736993611776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record053_result⟩)
 (.leaf ⟨(26, 7741286481920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record054_result⟩))
 (.branch 56
 (.leaf ⟨(26, 7775579111424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record055_result⟩)
 (.leaf ⟨(26, 7852485869568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record056_result⟩)))
 (.branch 59
 (.branch 58
 (.leaf ⟨(26, 7854031376448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record057_result⟩)
 (.leaf ⟨(26, 7930197835776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record058_result⟩))
 (.branch 60
 (.leaf ⟨(26, 7994185121792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record059_result⟩)
 (.leaf ⟨(26, 8041321892096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00012.record060_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14649 + i))) 0 61 :=
  interval_of_check _ 0 61 (by decide +kernel)

public theorem complete : Block 14649 14710 :=
  block_of_table results 14649 61 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0328
