module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00014Data
public import GraphInputsRow16Part00014Frames
public import GraphInputsRow16Part00014Leaves
public import GraphInputsRow16Part00014Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "acb1ac98e6c5a362d94e1b91e2785eac719c94e5c56352d54d1b51d2745dc8ea398ce3c4e938ccb3c2d4b1ae1b46c9b16f0761d4731e2749e1745c570dc8f0bca6198964384e078a5194954344d0770388ca318e1324d0b12c1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b49249b69b492492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 60), (facetIndex 65)]))
 (.leaf ([(facetIndex 73), (facetIndex 76)]))))
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 77)]))
 (.branch 5
 (.leaf ([(facetIndex 63)]))
 (.leaf ([(facetIndex 75)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1aa13000008801z2d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record018" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record018" "{\"ridges\":[[10,529],[13,546],[14,770],[32,529],[34,546],[38,769],[42,529],[45,770],[47,529],[47,546],[48,529],[49,529],[49,770],[51,546],[52,546],[53,546],[53,769],[60,564],[61,788],[64,792],[65,688],[72,564],[73,788],[76,792],[77,688]],\"owners\":[[10,529,[60,61,64,65],[32,42,47,48,49]],[32,529,[64,65],[10,42,47,48,49,60,61]],[42,529,[60,61,65],[10,32,47,48,49,64]],[47,529,[61,64],[10,32,42,48,49,60,65]],[48,529,[60,61,64],[10,32,42,47,49,65]],[49,529,[60,65],[10,32,42,47,48,61,64]],[13,546,[72,75,77],[34,47,51,52,53]],[34,546,[77],[13,47,51,52,53,72,75]],[47,546,[75],[13,34,51,52,53,72,77]],[51,546,[72,75,77],[13,34,47,52,53]],[52,546,[72,75],[13,34,47,51,53,77]],[53,546,[72,77],[13,34,47,51,52,75]],[38,769,[64],[14,45,49,53,61,63]],[53,769,[61,64],[14,38,45,49,63]],[14,770,[73,75,76],[38,45,49,53]],[45,770,[73,75],[14,38,49,53,76]],[49,770,[75],[14,38,45,53,73,76]],[60,564,[72],[]],[72,564,[60],[]],[61,788,[73],[]],[73,788,[61],[]],[64,792,[76],[]],[76,792,[64],[]],[65,688,[77],[]],[77,688,[65],[]]],\"edges\":[[34,[10,32,42,47,48,49,60,61,64,65,72,73,76,77]],[38,[13,34,47,51,52,53,60,63,65,72,75,77]],[44,[14,38,45,49,53,61,63,64,73,75,76]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,15,16,18,19],[-4,18,19],[-7,15,16,19],[-9,16,18],[-10,15,16,18],[-11,15,19],[-2,20,22,24],[-5,24],[-9,22],[-12,20,22,24],[-13,20,22],[-14,20,24],[-6,18],[-14,16,18],[-3,21,22,23],[-8,21,22],[-11,22],[-15,20],[-20,15],[-16,21],[-21,16],[-18,23],[-23,18],[-19,24],[-24,19],[-25,16,18],[-16,25],[-18,25],[-26,15,19],[-15,26],[-19,26],[-27,21,23],[-21,27],[-23,27],[-20,28],[-24,28],[-17,29],[-22,30],[-31,26,27],[-27,31],[-26,31],[-32,25,31],[-31,32],[-25,32],[-25,-31,33],[-30,34],[-29,34],[-34,35],[-28,35],[-28,-34,36],[-32,-36,37],[-33,-35,37],[-37],[1,4,7,9,10,11,15,16,18,19,20,21,23,24],[2,5,9,12,13,14,15,17,19,20,22,24],[3,6,8,11,14,16,17,18,21,22,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":529,\"a\":10,\"owners\":[60,61,64,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":32,\"owners\":[64,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":42,\"owners\":[60,61,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":47,\"owners\":[61,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":48,\"owners\":[60,61,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":49,\"owners\":[60,65]},{\"tag\":\"mate\",\"ridge\":546,\"a\":13,\"owners\":[72,75,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":34,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":47,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":51,\"owners\":[72,75,77]},{\"tag\":\"mate\",\"ridge\":546,\"a\":52,\"owners\":[72,75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":53,\"owners\":[72,77]},{\"tag\":\"mate\",\"ridge\":769,\"a\":38,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":769,\"a\":53,\"owners\":[61,64]},{\"tag\":\"mate\",\"ridge\":770,\"a\":14,\"owners\":[73,75,76]},{\"tag\":\"mate\",\"ridge\":770,\"a\":45,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":770,\"a\":49,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":564,\"a\":60,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":564,\"a\":72,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":788,\"a\":61,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":788,\"a\":73,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":792,\"a\":64,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":792,\"a\":76,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":688,\"a\":65,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":688,\"a\":77,\"owners\":[65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[61,64],\"full_literals\":[-25,16,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-16,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-18,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[60,65],\"full_literals\":[-26,15,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-15,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-19,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[73,76],\"full_literals\":[-27,21,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-21,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-23,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-24,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":63,\"full_literals\":[-17,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-22,30]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-31,26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,25,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-32,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[10,32,42,47,48,49,60,61,64,65,72,73,76,77]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[13,34,47,51,52,53,60,63,65,72,75,77]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[14,38,45,49,53,61,63,64,73,75,76]}]}"
  "p cnf 37 56\n-1 15 16 18 19 0\n-4 18 19 0\n-7 15 16 19 0\n-9 16 18 0\n-10 15 16 18 0\n-11 15 19 0\n-2 20 22 24 0\n-5 24 0\n-9 22 0\n-12 20 22 24 0\n-13 20 22 0\n-14 20 24 0\n-6 18 0\n-14 16 18 0\n-3 21 22 23 0\n-8 21 22 0\n-11 22 0\n-15 20 0\n-20 15 0\n-16 21 0\n-21 16 0\n-18 23 0\n-23 18 0\n-19 24 0\n-24 19 0\n-25 16 18 0\n-16 25 0\n-18 25 0\n-26 15 19 0\n-15 26 0\n-19 26 0\n-27 21 23 0\n-21 27 0\n-23 27 0\n-20 28 0\n-24 28 0\n-17 29 0\n-22 30 0\n-31 26 27 0\n-27 31 0\n-26 31 0\n-32 25 31 0\n-31 32 0\n-25 32 0\n-25 -31 33 0\n-30 34 0\n-29 34 0\n-34 35 0\n-28 35 0\n-28 -34 36 0\n-32 -36 37 0\n-33 -35 37 0\n-37 0\n1 4 7 9 10 11 15 16 18 19 20 21 23 24 0\n2 5 9 12 13 14 15 17 19 20 22 24 0\n3 6 8 11 14 16 17 18 21 22 23 0\n"
  "57 32 0 43 44 40 41 27 28 33 34 30 31 4 3 5 2 1 6 19 25 54 0\n58 -36 0 57 53 51 0\n59 31 0 57 40 42 33 34 20 22 26 0\n60 28 -26 0 35 36 18 24 29 0\n61 16 18 0 58 59 14 21 13 23 32 39 60 50 46 47 38 37 17 15 16 56 0\n62 25 0 27 28 61 0\n63 33 0 62 59 45 0\n64 -35 0 63 53 52 0\n65 -34 0 64 48 0\n66 -28 0 64 49 0\n67 -30 0 65 46 0\n68 -29 0 65 47 0\n69 -20 0 66 35 0\n70 -24 0 66 36 0\n71 -22 0 67 38 0\n72 -17 0 68 37 0\n73 -15 0 69 18 0\n74 -2 0 69 71 70 7 0\n75 -13 0 69 71 11 0\n76 -5 0 70 8 0\n77 -19 0 70 24 0\n78 -14 0 70 69 12 0\n79 -12 0 70 71 69 10 0\n80 -9 0 71 9 0\n81 0 79 77 76 74 75 80 73 78 72 69 71 70 55 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9ab1a398b68b86e4789e17a69c64e52d62d1b51d2745dc8ea398ce3c4d932ce4b52e2b1ae1b26c5b31e2745c570de0f43c8f0bf0a468a6198961381ec2519294652544d0770388ca318d1324e0b42c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a49a493493492492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 40), (facetIndex 43), (facetIndex 47), (facetIndex 59), (facetIndex 68)]))
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 37), (facetIndex 45), (facetIndex 57), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 38), (facetIndex 39), (facetIndex 46)]))
 (.leaf ([(facetIndex 29), (facetIndex 55), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 67)]))
 (.leaf ([(facetIndex 36), (facetIndex 42), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)])))
 (.branch 7
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 44)]))
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 54)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "410466600310388855550217057022152217013z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 60)]))
 (.leaf ([(facetIndex 65), (facetIndex 69)])))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨1, sparse_nat% "22z10;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 2
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0017 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record026" 30

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record026" "{\"ridges\":[[14,769],[21,521],[28,776],[32,521],[44,521],[47,769],[51,545],[56,521],[59,521],[60,521],[68,776]],\"owners\":[[51,545,[56,60],[13,36,42,49,50]],[14,769,[21,59],[47,51]],[47,769,[21],[14,51,59]],[28,776,[21,59],[68]],[68,776,[21],[28,59]]],\"edges\":[[44,[14,21,28,47,51,59,68]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-5],[-9,-7],[-11,-4],[-11,-5],[-11,-6],[-11,-10],[-12,-11],[-14,-4],[-14,-6],[-14,-7],[-14,-10],[-15,-14],[-16,-12],[-2,-5,-14],[-2,-7,-11],[-5,-13,-14],[-7,-11,-13],[-9,11,14],[-1,2,13],[-8,2],[-3,2,13],[-17,2],[-18,4,10,12],[-19,15,16],[-20,5,6,7],[-21,18],[-22,21],[-23,19],[-24,20],[-25,24],[-26,23,25],[-27,25],[-28,22,27],[-28,26],[28],[-29,11,14],[-30,29],[30],[1,2,3,8,9,13,17]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":51,\"b\":32},{\"tag\":\"incompatible\",\"a\":51,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":29},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":41},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":67,\"b\":58},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[21,32,60]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[21,44,56]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[32,59,60]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[44,56,59]},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[56,60]},{\"tag\":\"mate\",\"ridge\":769,\"a\":14,\"owners\":[21,59]},{\"tag\":\"mate\",\"ridge\":769,\"a\":47,\"owners\":[21]},{\"tag\":\"mate\",\"ridge\":776,\"a\":28,\"owners\":[21,59]},{\"tag\":\"mate\",\"ridge\":776,\"a\":68,\"owners\":[21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[29,55,58],\"full_literals\":[-18,4,10,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[64,67],\"full_literals\":[-19,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,41,44],\"full_literals\":[-20,5,6,7]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-21,false,18],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-22,false,21],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-23,19,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-24,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-25,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-26,23,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-27,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-28,22,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-28,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[56,60],\"full_literals\":[-29,11,14]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,29,false],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[14,21,28,47,51,59,68]}]}"
  "p cnf 30 39\n-9 -5 0\n-9 -7 0\n-11 -4 0\n-11 -5 0\n-11 -6 0\n-11 -10 0\n-12 -11 0\n-14 -4 0\n-14 -6 0\n-14 -7 0\n-14 -10 0\n-15 -14 0\n-16 -12 0\n-2 -5 -14 0\n-2 -7 -11 0\n-5 -13 -14 0\n-7 -11 -13 0\n-9 11 14 0\n-1 2 13 0\n-8 2 0\n-3 2 13 0\n-17 2 0\n-18 4 10 12 0\n-19 15 16 0\n-20 5 6 7 0\n-21 18 0\n-22 21 0\n-23 19 0\n-24 20 0\n-25 24 0\n-26 23 25 0\n-27 25 0\n-28 22 27 0\n-28 26 0\n28 0\n-29 11 14 0\n-30 29 0\n30 0\n1 2 3 8 9 13 17 0\n"
  "40 26 0 35 34 0\n41 29 0 38 37 0\n42 -9 -20 0 1 2 25 5 9 18 0\n43 13 2 9 0 22 20 19 21 39 0\n44 -7 -13 0 41 10 17 36 0\n45 -11 7 -20 0 4 5 25 0\n46 -13 -20 0 41 44 45 36 9 16 25 0\n47 -14 -20 0 42 46 43 9 10 14 25 0\n48 -20 0 41 42 46 43 47 36 15 45 0\n49 -24 0 48 29 0\n50 -25 0 49 30 0\n51 -27 0 50 32 0\n52 23 0 50 40 31 0\n53 22 0 51 35 33 0\n54 19 0 52 28 0\n55 21 0 53 27 0\n56 18 0 55 26 0\n57 -11 0 56 3 6 7 23 0\n58 14 0 57 41 36 0\n59 -4 0 58 8 0\n60 -10 0 58 11 0\n61 -15 0 58 12 0\n62 12 0 60 59 56 23 0\n63 16 0 61 54 24 0\n64 0 63 62 13 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2eaa6998e6c59968b8ae1b91e2785e2e6a5994e5c55958b4ad1b51d2745dc8ea398ce3c4d932ce2b2ad1b26c5b0ee8761e4751cc789ca719e1715e0f43c8f0bc6ac19162584e07869c15152544d0770388ca318d1324c4b0ac1b81d0721c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d26d249b6d26d2492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 33), (facetIndex 42), (facetIndex 57), (facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 31), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 60)]))
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 72)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 29), (facetIndex 32), (facetIndex 37), (facetIndex 39), (facetIndex 49), (facetIndex 61), (facetIndex 73)]))
 (.leaf ([(facetIndex 35), (facetIndex 45), (facetIndex 46), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53)])))
 (.branch 6
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 34), (facetIndex 36), (facetIndex 38), (facetIndex 40)]))
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 47), (facetIndex 48)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a00248001900126491ed26c3575d94335dz15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record029" "{\"atoms\":[]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record029" 0

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record029" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[]],\"atoms\":[],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 0 1\n 0\n"
  "2 0 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00014.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00014.record029
