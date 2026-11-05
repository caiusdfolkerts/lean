module
prelude
import GraphInputsRow26Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0324
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 5892764565512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record000_result⟩)
 (.leaf ⟨(26, 5895660519424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 5899150164996), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record002_result⟩)
 (.leaf ⟨(26, 5899414405636), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 5899414536193), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record004_result⟩)
 (.leaf ⟨(26, 5899687035904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 5904116219904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 5904380461056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record007_result⟩)
 (.leaf ⟨(26, 5972833599488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 5974905651200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record009_result⟩)
 (.leaf ⟨(26, 5974913974272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 5998538407936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record011_result⟩)
 (.leaf ⟨(26, 6340532011264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(26, 6343310180352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record013_result⟩)
 (.leaf ⟨(26, 6379104503040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record014_result⟩))
 (.branch 16
 (.leaf ⟨(26, 6379104568320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 6379112760324), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record016_result⟩)
 (.leaf ⟨(26, 6379377000964), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 6379377131521), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record018_result⟩)
 (.leaf ⟨(26, 6379649631232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 6379918065664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record020_result⟩)
 (.leaf ⟨(26, 6443268835328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 6447563800576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record022_result⟩)
 (.leaf ⟨(26, 6451871350784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 6456149540864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 6487088824320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record025_result⟩)
 (.leaf ⟨(26, 6511854094336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(26, 6524592390144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record027_result⟩)
 (.leaf ⟨(26, 6524600713216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record028_result⟩))
 (.branch 30
 (.leaf ⟨(26, 6548361314304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 6559027429376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record030_result⟩)
 (.leaf ⟨(26, 6633730703744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 6633732784512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record032_result⟩)
 (.leaf ⟨(26, 6701436731400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 6701511180544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 6701513261312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record035_result⟩)
 (.leaf ⟨(26, 6701568851976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14512 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 14512 14549 :=
  block_of_table results 14512 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0324
