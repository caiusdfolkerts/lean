module
prelude
import GraphInputsRow26Part00058Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0374
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 27798256255232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 27798313896064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record001_result⟩)
 (.leaf ⟨(26, 27801533548672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 27811333013504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 27814379128960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record004_result⟩)
 (.leaf ⟨(26, 27868186869760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 27874673574144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 27903536463872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record007_result⟩)
 (.leaf ⟨(26, 27903666438400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 27915242766336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record009_result⟩)
 (.leaf ⟨(26, 27915251089408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 27936902103296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record011_result⟩)
 (.leaf ⟨(26, 27936910491648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(26, 27939048538368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 27939050684416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record014_result⟩)
 (.leaf ⟨(26, 27939056926720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(26, 27943258833152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 27943269042176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record017_result⟩)
 (.leaf ⟨(26, 27943661486144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(26, 27943728586816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 27971269181440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record020_result⟩)
 (.leaf ⟨(26, 28041080242432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 28041080307712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record022_result⟩)
 (.leaf ⟨(26, 28047785934848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 28048967602192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record024_result⟩)
 (.leaf ⟨(26, 28076495437824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00058.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16937 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 16937 16963 :=
  block_of_table results 16937 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0374
