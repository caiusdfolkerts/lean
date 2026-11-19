module
prelude
import GraphInputsRow26Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0347
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 18618897137664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 18619020935168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record001_result⟩)
 (.leaf ⟨(26, 18619029258240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 18619489599488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 18634332192768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record004_result⟩)
 (.leaf ⟨(26, 18732040667264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 18744522915968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 18805927510272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record007_result⟩)
 (.leaf ⟨(26, 18817394835712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 18817394900992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record009_result⟩)
 (.leaf ⟨(26, 18817939963904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 18847803457568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record011_result⟩)
 (.leaf ⟨(26, 18848000589888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(26, 18883236872448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 18883236937728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record014_result⟩)
 (.leaf ⟨(26, 18939333640448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 18939342028800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record016_result⟩)
 (.leaf ⟨(26, 18943626510592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 18943634898944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record018_result⟩)
 (.leaf ⟨(26, 18951956398080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(26, 18952216412416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 18952226881536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record021_result⟩)
 (.leaf ⟨(26, 18954497048832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 18955976638720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record023_result⟩)
 (.leaf ⟨(26, 18956249268224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 18956513509376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record025_result⟩)
 (.leaf ⟨(26, 18956521832448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record026_result⟩))))))
 (.branch 41
 (.branch 34
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 18956645629952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 18956786073600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record028_result⟩)
 (.leaf ⟨(26, 18960806379520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(26, 18960814702592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record030_result⟩)
 (.leaf ⟨(26, 18962349883648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record031_result⟩))
 (.branch 33
 (.leaf ⟨(26, 18962886754304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record032_result⟩)
 (.leaf ⟨(26, 18962895077376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record033_result⟩))))
 (.branch 37
 (.branch 35
 (.leaf ⟨(26, 18974262722816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 18985033744512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record035_result⟩)
 (.leaf ⟨(26, 19023695740928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(26, 19041947779328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record037_result⟩)
 (.leaf ⟨(26, 19059028557824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record038_result⟩))
 (.branch 40
 (.leaf ⟨(26, 19059127648256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record039_result⟩)
 (.leaf ⟨(26, 19074506588416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record040_result⟩)))))
 (.branch 48
 (.branch 44
 (.branch 42
 (.leaf ⟨(26, 19076504158464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record041_result⟩)
 (.branch 43
 (.leaf ⟨(26, 19076512546816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record042_result⟩)
 (.leaf ⟨(26, 19080797028608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(26, 19080805416960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record044_result⟩)
 (.leaf ⟨(26, 19087046477952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record045_result⟩))
 (.branch 47
 (.leaf ⟨(26, 19089391157248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record046_result⟩)
 (.leaf ⟨(26, 19093419884544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record047_result⟩))))
 (.branch 51
 (.branch 49
 (.leaf ⟨(26, 19097976897536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record048_result⟩)
 (.branch 50
 (.leaf ⟨(26, 19097985220608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record049_result⟩)
 (.leaf ⟨(26, 19098513702912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record050_result⟩)))
 (.branch 53
 (.branch 52
 (.leaf ⟨(26, 19099925151744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record051_result⟩)
 (.leaf ⟨(26, 19099933474816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record052_result⟩))
 (.branch 54
 (.leaf ⟨(26, 19100057272320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record053_result⟩)
 (.leaf ⟨(26, 19100065595392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00031.record054_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15670 + i))) 0 55 :=
  interval_of_check _ 0 55 (by decide +kernel)

public theorem complete : Block 15670 15725 :=
  block_of_table results 15670 55 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0347
