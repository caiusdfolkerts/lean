module
prelude
import GraphInputsRow24Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0120
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 2420424343808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record000_result⟩)
 (.leaf ⟨(24, 2420424409088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 2420625711104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 2446667579648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record003_result⟩)
 (.leaf ⟨(24, 2446667644928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 2453040889856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 2454716580096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record006_result⟩)
 (.leaf ⟨(24, 2454716645376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 2454720611584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 2455257481217), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_result⟩)
 (.leaf ⟨(24, 2459552465024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 2469679596800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record011_result⟩)
 (.leaf ⟨(24, 2469811781888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 2469820170240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 2470018351104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record014_result⟩)
 (.leaf ⟨(24, 2470212305152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 2470220693504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 2522695663616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record017_result⟩)
 (.leaf ⟨(24, 2583838097664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 2583838162944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 2584240734336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record020_result⟩)
 (.leaf ⟨(24, 2588131033088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 2588401483904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record022_result⟩)
 (.leaf ⟨(24, 2590277468160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 2601017966592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 2601410134144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record025_result⟩)
 (.leaf ⟨(24, 2601546448896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(24, 2605302448384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 2605306675200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record028_result⟩)
 (.leaf ⟨(24, 2605310836736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(24, 2605570883712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 2605839319040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_result⟩)
 (.leaf ⟨(24, 2605843480576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(24, 2607250702592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 2607259090944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record034_result⟩)
 (.leaf ⟨(24, 2607382823168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(24, 2607387049984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 2607391211520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record037_result⟩)
 (.leaf ⟨(24, 2607457271808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(24, 2607651258496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 2607851520128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record040_result⟩)
 (.leaf ⟨(24, 2652555477248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(24, 2675976470528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 2686715986176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record043_result⟩)
 (.leaf ⟨(24, 2686843945216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record044_result⟩)))))))
 (.branch 68
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf ⟨(24, 2686848106752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record045_result⟩)
 (.leaf ⟨(24, 2686848172032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record046_result⟩))
 (.branch 48
 (.leaf ⟨(24, 2686914167040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record047_result⟩)
 (.branch 49
 (.leaf ⟨(24, 2686914232320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record048_result⟩)
 (.leaf ⟨(24, 2687116542080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record049_result⟩))))
 (.branch 53
 (.branch 51
 (.leaf ⟨(24, 2687118622848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(24, 2789191286912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record051_result⟩)
 (.leaf ⟨(24, 2796707479568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(24, 2801801462016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record053_result⟩)
 (.branch 55
 (.leaf ⟨(24, 2801805656192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record054_result⟩)
 (.leaf ⟨(24, 2827508351232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record055_result⟩)))))
 (.branch 62
 (.branch 59
 (.branch 57
 (.leaf ⟨(24, 2828919734288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record056_result⟩)
 (.branch 58
 (.leaf ⟨(24, 2836094091520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record057_result⟩)
 (.leaf ⟨(24, 2934280569088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(24, 2981986631936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record059_result⟩)
 (.branch 61
 (.leaf ⟨(24, 2981995020288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record060_result⟩)
 (.leaf ⟨(24, 2982193201152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record061_result⟩))))
 (.branch 65
 (.branch 63
 (.leaf ⟨(24, 2982387155200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record062_result⟩)
 (.branch 64
 (.leaf ⟨(24, 2982395543552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record063_result⟩)
 (.leaf ⟨(24, 3034807631888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(24, 3096012947712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(24, 3096013012992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record066_result⟩)
 (.leaf ⟨(24, 3096415584384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record067_result⟩))))))
 (.branch 79
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf ⟨(24, 3098093322496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record068_result⟩)
 (.leaf ⟨(24, 3098093387776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record069_result⟩))
 (.branch 71
 (.leaf ⟨(24, 3102386257920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record070_result⟩)
 (.branch 72
 (.leaf ⟨(24, 3102452318208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record071_result⟩)
 (.leaf ⟨(24, 3102656708736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record072_result⟩))))
 (.branch 76
 (.branch 74
 (.leaf ⟨(24, 3115801673728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record073_result⟩)
 (.branch 75
 (.leaf ⟨(24, 3119425552640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record074_result⟩)
 (.leaf ⟨(24, 3119433940992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record075_result⟩)))
 (.branch 77
 (.leaf ⟨(24, 3119557673216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record076_result⟩)
 (.branch 78
 (.leaf ⟨(24, 3119561900032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record077_result⟩)
 (.leaf ⟨(24, 3119566061568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record078_result⟩)))))
 (.branch 85
 (.branch 82
 (.branch 80
 (.leaf ⟨(24, 3119632121856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record079_result⟩)
 (.branch 81
 (.leaf ⟨(24, 3119826108544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record080_result⟩)
 (.leaf ⟨(24, 3120026370176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record081_result⟩)))
 (.branch 83
 (.leaf ⟨(24, 3120094543872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record082_result⟩)
 (.branch 84
 (.leaf ⟨(24, 3120098705408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record083_result⟩)
 (.leaf ⟨(24, 3131329052672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record084_result⟩))))
 (.branch 88
 (.branch 86
 (.leaf ⟨(24, 3135886163968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record085_result⟩)
 (.branch 87
 (.leaf ⟨(24, 3153330208768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record086_result⟩)
 (.leaf ⟨(24, 3153334370304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record087_result⟩)))
 (.branch 89
 (.leaf ⟨(24, 3157077950464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record088_result⟩)
 (.branch 90
 (.leaf ⟨(24, 3157081981952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record089_result⟩)
 (.leaf ⟨(24, 3157337997440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record090_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7935 + i))) 0 91 :=
  interval_of_check _ 0 91 (by decide +kernel)

public theorem complete : Block 7935 8026 :=
  block_of_table results 7935 91 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0120
