module
prelude
import GraphInputsRow16Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0013
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 16840856707328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 16873070592000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record001_result⟩)
 (.leaf ⟨(16, 16918564577280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 16918565617664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record003_result⟩)
 (.leaf ⟨(16, 16944925310976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 16975996848128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record005_result⟩)
 (.leaf ⟨(16, 16976135211008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(16, 17010236883200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 17010373230592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record008_result⟩)
 (.leaf ⟨(16, 17010381553664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 17010620956672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_result⟩)
 (.leaf ⟨(16, 17014533980160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 17014806544384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record012_result⟩)
 (.leaf ⟨(16, 17015318511616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(16, 17023103074304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 17023639879680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record015_result⟩)
 (.leaf ⟨(16, 17040282877952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 17045964029952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record017_result⟩)
 (.leaf ⟨(16, 17081374933248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 17081379160064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record019_result⟩)
 (.leaf ⟨(16, 17081382736128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(16, 17082435666176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 17082435731456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record022_result⟩)
 (.leaf ⟨(16, 17082464928000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 17082473316352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record024_result⟩)
 (.leaf ⟨(16, 17082964541696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 17085938352128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record026_result⟩)
 (.leaf ⟨(16, 17086766186496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record027_result⟩))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf ⟨(16, 17086856888576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 17087026200832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record029_result⟩)
 (.leaf ⟨(16, 17087030427648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 17087125291264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record031_result⟩)
 (.leaf ⟨(16, 17087137320960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 17090480705792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record033_result⟩)
 (.leaf ⟨(16, 17090786427136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(16, 17091323297792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 17091331620864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record036_result⟩)
 (.leaf ⟨(16, 17091554508800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(16, 17091595862016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record038_result⟩)
 (.leaf ⟨(16, 17103669199104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record039_result⟩))
 (.branch 41
 (.leaf ⟨(16, 17103805546496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record040_result⟩)
 (.leaf ⟨(16, 17103813869568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record041_result⟩)))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf ⟨(16, 17103945990144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record042_result⟩)
 (.branch 44
 (.leaf ⟨(16, 17104036757504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record043_result⟩)
 (.leaf ⟨(16, 17104573562880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(16, 17106888851712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record045_result⟩)
 (.leaf ⟨(16, 17107157319680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record046_result⟩))
 (.branch 48
 (.leaf ⟨(16, 17107165642752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record047_result⟩)
 (.leaf ⟨(16, 17107660574720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record048_result⟩))))
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf ⟨(16, 17146872660224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record049_result⟩)
 (.leaf ⟨(16, 17146881048576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record050_result⟩))
 (.branch 52
 (.leaf ⟨(16, 17154393571328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record051_result⟩)
 (.leaf ⟨(16, 17154401698048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record052_result⟩)))
 (.branch 55
 (.branch 54
 (.leaf ⟨(16, 17154653585664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record053_result⟩)
 (.leaf ⟨(16, 17154657812480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record054_result⟩))
 (.branch 56
 (.leaf ⟨(16, 17154665615360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record055_result⟩)
 (.leaf ⟨(16, 17154682390528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record056_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (893 + i))) 0 57 :=
  interval_of_check _ 0 57 (by decide +kernel)

public theorem complete : Block 893 950 :=
  block_of_table results 893 57 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0013
