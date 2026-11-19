module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00014Data
public import GraphInputsRow16Part00014Frames
public import GraphInputsRow16Part00014Leaves
public import GraphInputsRow16Part00014Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002
def vertexColumn : Fields := ⟨10, hexnat% "cb0dcca8dac98d62d876c38ce8b92e2785eca4d9c94d58d4b51d70da364d3362d4b49d1772334d332cc73c2d8b52ccb8ad2b26c5bc1cc789d2729c6783d0f0bc1f258560d88e13b21c2625254550d60d2344d48c9314c3342c8b12c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da49a6d24d2492492692492492692692492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e2fffff48fffc000000", 7696581394432, hexnat% "800000200000000000", hexnat% "1100000800000000000", hexnat% "400000100000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fef56ef00bca4000000", 263882790666240, hexnat% "100000010018000000", 15668040695808, 11605776239733768192, 576460766262067200]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3eed4e0e709ffc000000", 11529496521045180416, 139611588448485376, hexnat% "20000002000000000", 16767552323584, hexnat% "1101000800000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3cee1d48cfec000000", 193720204918784, 135107989089550336, 1153484454560268288, hexnat% "1c30000000000000000", 7696581394432]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e2fe91ffffffc000000", 63050394783186944, 1585267068834414592, hexnat% "1100000000000000000", hexnat% "c00000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c1 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fef600eb7bed4000000", 352122893762560, 2161727821137838080, 9295438426985725952, hexnat% "100020000028000000", 58546795155816448]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f3ff9fd8fff7c000000", 105555263750144, 432908514180988928, hexnat% "c00000000000000000", 17592186044416]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f3ff1ffcfef7c000000", 52845277609984, 864691130602618880, hexnat% "c00000000000000000", 144115188075855872]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c1 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f3ff13d8ffffc000000", 123145302310912, 54606145481867264, 1008806316530991104, hexnat% "c00000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3ffffffffffffc000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c19 c15
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c20 c13
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3fdeff4ffffc000000", 2377900603251621888, 193514046488576, hexnat% "1c00000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3fffff08fffc000000", 7696581394432, hexnat% "400000100000000000", 246290604621824, hexnat% "1800000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c1 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff57ee00be6c000000", 2886807361144487936, 16767820759040, 263882790666240, 9223653511831486464, 6442450944]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c26 c22
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3cc8ff4feffc000000", 2377900603251621888, 1585267068834414592, 193582765965312, hexnat% "1c30000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3fe91ffffffc000000", 63050394783186944, hexnat% "400200000000000000", 1441151880758558720, hexnat% "1800000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c1 c29
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7f620eb7be5c000000", 70375186628608, hexnat% "1800000000000000000", 9223662582802415616, 139611588985356288, 2017612633061982208]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f3f502e8ffffc000000", 130604389193744384, hexnat% "c00000000000000000", 123145302310912, 1008806316530991104, 11529496521045180416]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e3ce90f78ffdc000000", 1585267068834414592, 7697118265344, hexnat% "1000020800000000000", 58546795155816448, hexnat% "c30000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff400e00bf4c000000", 263882790666240, 11529496521045180416, 2161727821137838080, 16767820759040, 139611588985356288, 2147483648]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c37 c32
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c38 c28
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c39 c27
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c40 c21
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c41 c11
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c42 c7
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c43 c5
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c44 c4
  c45
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004
def vertexColumn : Fields := ⟨10, hexnat% "32c3732a368ba1eb2635936c38ce8b92e2785e0fb29364b91e725356354d70da364d3362d4b49d1743dc8cd34ccb31cf0b32e2b4acab1ac9b16c3bc1d8751cc789d2745c3783d0f0bc1f258562384ec8629c14951560d2344d48c9314c3322c4b0ad0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4da6d269b69369249a4d2493492492492692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [545290104864768, hexnat% "44002000000000000", 558446353793941504, hexnat% "9300000000100000000", 61203283968, 2312598408654749696]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8046003e10f7f000000", hexnat% "1300000000000000000", 16011638079488, 558446353793941504, 6755811757916160]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [545290104864768, hexnat% "44002000000000000", 558446353793941504, 65498251264, hexnat% "9300000000000000000", 2312598408654749696]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44002018020000000", 248558615789568, 4432540467200, 558446353793941504, hexnat% "9002001080101000000", hexnat% "300018006000000000", 26944208896]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027
def vertexColumn : Fields := ⟨10, hexnat% "aaa6a3ab1ac98b6c3a2e2b86e4789e17aa99a4e9c67252d70d8b4ad1b51d2745dc8ea398ce3c4d932cf0ba2e4b32e2b2ac6b86d1b16f0751e2749ca725c570de0f43c8f0bc9a199161381e264654544d0770388ca318d1324e0b22c4b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6924db6db6d2492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3801c278fffe000000", 424411488321536, 16892896649150464, hexnat% "400200010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3801c382ebfe000000", hexnat% "400200050000000000", 9077653898264576, 1134695999864832, 52776558133248, 6755399441055744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40023e7fbffe000000", 422487342972928, 126100789566373888, hexnat% "380000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001e37fe0de000000", hexnat% "400200000800000000", hexnat% "280000000000000000", 95026151424, 8022041131220992]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40023fbfb79e000000", 126100789566373888, hexnat% "380000000000000000", 35970351104, 70643622084608]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4002000788ca000000", 844768527515648, 126100789566373888, hexnat% "380000000000000000", 132079169830912, 8022058847961088, 9007207844675584]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record027
