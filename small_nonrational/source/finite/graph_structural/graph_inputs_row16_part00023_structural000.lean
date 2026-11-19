module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00023Data
public import GraphInputsRow16Part00023Frames
public import GraphInputsRow16Part00023Leaves
public import GraphInputsRow16Part00023Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record034
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034
def vertexColumn : Fields := ⟨10, hexnat% "2b4a723c4eaa6598b6a394e8b92e2785e0fab1ca6998e539a9565a56352d68d9354d8b52d8749d1743da8d634ccb3a2e2b4ad1b26c5b0ee8751cc789d2729c6715e0f43c8f0bd4a258361381e52685894950d60d1341d50d2324c3342c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69a6d24db6d34924934926926d2492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4102fef71fffe000000", hexnat% "1000000000000000000", hexnat% "80000020000000000", hexnat% "200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11007ef705ffe000000", 2882303761517117440, 1786706395136, hexnat% "80000020000000000", hexnat% "4200000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11003ef00497e000000", hexnat% "4280000000000000000", 576460840350253056, 54563264528384, 72567767433216, 2594073393955340288]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82faf023232000000", hexnat% "1000040004808000000", 106652627894272, hexnat% "4300000000000000000", 24763170816, 18141941858304]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1804ab637ffe000000", hexnat% "1000040000000000000", 18141941858304, 649644246248194048, hexnat% "4200000000000000000", 2449958197289549824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100046273efee000000", hexnat% "4380000000000000000", 3026419018312450048, 39687971984637952, 72057594037927936]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4382e2f1013a2000000", 52814675968, 108086391325327360, hexnat% "1000040004000000000", 108851651149824, 687194767360]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100026200490a000000", 108851651149824, hexnat% "4380000000020000000", 18279380811776, 39687971984637952, 3242591731706757120, 97777614848]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c13 c4
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record034_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record034

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035
def vertexColumn : Fields := ⟨10, hexnat% "acb2aa6a3a4eaa6598b6a394e8b92e2785e0fab1ca6998e539a95652d68d5362d4b49d1743dc8ea358e938cd332cf0ba2e4b8ad2b86d1b26c5b0ee8751cc789d2729c6715e0f43c8f0bd4a258361381e524950d44d0768350e2348c930ce0b42c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da69b4936db6d34da492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000eb5f7ffe000000", hexnat% "4000800000000000000", 1161634034745344, 2377900603251621888, hexnat% "10800000000000000000", 4644337115725824]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20007f7f7b5a000000", hexnat% "4000800000000000000", 19931332608, 141287244169216, 2413929400270585856, hexnat% "10c00000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102020778ff3a2000000", 52814675968, 2322168557862912, hexnat% "800100200000000000", hexnat% "4000800100000000000", hexnat% "400080000010000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20006fdfeb7a000000", hexnat% "4000800000000000000", 88113938432, 4538783999459328, 2413929400270585856, hexnat% "10c00000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17169924690542592, hexnat% "4000800000900000000", 844434593808384, 2431943799316938752, hexnat% "10e00000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000816ffe91e000000", 98247376896, 2431943798780067840, hexnat% "10e00000000000000000", 11540474045136896]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14e029c0dafffe000000", 6227633859723264, 2538772348534784, 9007199254740992]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400083feebfee000000", 2431943798780067840, hexnat% "10e00000000000000000", 18966844014592]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000809ffe93e000000", 2431943798780067840, hexnat% "10e00000000000000000", 1125987953672192, 9570158871838720, 4503599627370496]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040cf2122000000", hexnat% "4000800104808000000", hexnat% "10002010000080000000", hexnat% "800100208004000000", 1125985806188544, 12103433662234624, hexnat% "400080000010000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00023.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00023.record035
