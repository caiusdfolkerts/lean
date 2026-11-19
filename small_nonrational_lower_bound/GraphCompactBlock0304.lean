module
prelude
import GraphInputsRow25Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0304
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 20278893674496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record000_result⟩)
 (.leaf ⟨(25, 20381377265664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 20385670135808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record002_result⟩)
 (.leaf ⟨(25, 20393991634944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 20412123582720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record004_result⟩)
 (.leaf ⟨(25, 20428152143872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 20688190636032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record006_result⟩)
 (.leaf ⟨(25, 20688198959104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(25, 20688459038720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record008_result⟩)
 (.leaf ⟨(25, 20688591159296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record009_result⟩))
 (.branch 11
 (.leaf ⟨(25, 20690279333888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record010_result⟩)
 (.leaf ⟨(25, 20694572204032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(25, 20694638264320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record012_result⟩)
 (.leaf ⟨(25, 20710366920832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record013_result⟩))
 (.branch 15
 (.leaf ⟨(25, 20711611564032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record014_result⟩)
 (.branch 16
 (.leaf ⟨(25, 20723514998784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record015_result⟩)
 (.leaf ⟨(25, 20724022804480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(25, 20727807868928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record017_result⟩)
 (.leaf ⟨(25, 20727915151360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record018_result⟩))
 (.branch 20
 (.leaf ⟨(25, 20728072110080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record019_result⟩)
 (.leaf ⟨(25, 20728183554048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(25, 20732612444672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record021_result⟩)
 (.leaf ⟨(25, 20736505053184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record022_result⟩))
 (.branch 24
 (.leaf ⟨(25, 20744692187264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record023_result⟩)
 (.leaf ⟨(25, 20748987170816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(25, 20749255573504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record025_result⟩)
 (.leaf ⟨(25, 20758856269824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record026_result⟩))
 (.branch 28
 (.leaf ⟨(25, 20792608063488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record027_result⟩)
 (.leaf ⟨(25, 20800937656320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(25, 20824304189440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record029_result⟩)
 (.leaf ⟨(25, 20824820318208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record030_result⟩))
 (.branch 32
 (.leaf ⟨(25, 20826900692992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 20833149911040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record032_result⟩)
 (.leaf ⟨(25, 20839382941696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record033_result⟩)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ⟨(25, 20896260587776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record034_result⟩)
 (.leaf ⟨(25, 20929529282816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record035_result⟩))
 (.branch 37
 (.leaf ⟨(25, 20931130982400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record036_result⟩)
 (.leaf ⟨(25, 20977905860608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(25, 21007368716288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record038_result⟩)
 (.leaf ⟨(25, 21015946068608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record039_result⟩))
 (.branch 41
 (.leaf ⟨(25, 21076086095872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record040_result⟩)
 (.leaf ⟨(25, 21119160565760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record041_result⟩))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ⟨(25, 21257072410624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record042_result⟩)
 (.leaf ⟨(25, 21350955614208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record043_result⟩))
 (.branch 45
 (.leaf ⟨(25, 21367598612480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record044_result⟩)
 (.leaf ⟨(25, 21374041096448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 21378338193408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record046_result⟩)
 (.leaf ⟨(25, 21378610757632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 21379007119360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record048_result⟩)
 (.branch 50
 (.leaf ⟨(25, 21382631063552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record049_result⟩)
 (.leaf ⟨(25, 21383167868928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record050_result⟩))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(25, 21384711438336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record051_result⟩)
 (.leaf ⟨(25, 21397596291072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record052_result⟩))
 (.branch 54
 (.leaf ⟨(25, 21401891241984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record053_result⟩)
 (.leaf ⟨(25, 21402023362560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(25, 21446426394624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record055_result⟩)
 (.leaf ⟨(25, 21462623195264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record056_result⟩))
 (.branch 58
 (.leaf ⟨(25, 21514053779456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record057_result⟩)
 (.branch 59
 (.leaf ⟨(25, 21515382816768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record058_result⟩)
 (.leaf ⟨(25, 21519543566336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record059_result⟩)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf ⟨(25, 21519667363840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record060_result⟩)
 (.leaf ⟨(25, 21522887016448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record061_result⟩))
 (.branch 63
 (.leaf ⟨(25, 21527047442560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record062_result⟩)
 (.leaf ⟨(25, 21528120918656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record063_result⟩)))
 (.branch 66
 (.branch 65
 (.leaf ⟨(25, 21535771869184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record064_result⟩)
 (.leaf ⟨(25, 21588260945920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record065_result⟩))
 (.branch 67
 (.leaf ⟨(25, 21591472275456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record066_result⟩)
 (.branch 68
 (.leaf ⟨(25, 21596582445056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record067_result⟩)
 (.leaf ⟨(25, 21596976726016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00014.record068_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13247 + i))) 0 69 :=
  interval_of_check _ 0 69 (by decide +kernel)

public theorem complete : Block 13247 13316 :=
  block_of_table results 13247 69 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0304
