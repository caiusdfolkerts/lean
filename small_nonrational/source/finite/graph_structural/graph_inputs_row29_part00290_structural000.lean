module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00290Data
public import GraphInputsRow29Part00290Frames
public import GraphInputsRow29Part00290Leaves
public import GraphInputsRow29Part00290Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00290.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002
def vertexColumn : Fields := ⟨10, hexnat% "32c9b16c3723c4f0bc1f32a9a96a36a3a4e87ac9a66598d68d9361db0ea398e9394e33a2e4b86e8791e2785e0fb299a569366394e4b9c9665594d58d5352d70da358d9354d3362d4b4ad1b61d4749d1743dc8e6358cd38cd331cf0ba2d8b92d4b32e2b4ac6b86d1b0ef07a1d8791d4731e2749c6785d170de0f43c8f13c2f07c781d09a16896158718a5291a4991643989525194951543524c5382d0b22c4b06e0741c8711c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d36d369b69b4db6db6db49a4924924924db6da4d36926da6d2492492492492492492493449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨111, by decide⟩, ⟨114, by decide⟩, ⟨118, by decide⟩, ⟨121, by decide⟩, ⟨125, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000000ddfb81a702010011e80000000", hexnat% "408000000000000062062000000000", hexnat% "2040000204000010080080000000000", 546182401097728, 2237163114896293888]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24400003ff80271209e082080000000", hexnat% "2000000c000018000000001e00000000", hexnat% "8000000000000060070000000000", hexnat% "1c00000000000000000000000", 2233785415175766016, 546182401097728]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2048001fc780271208209e080000000", hexnat% "2000000c000018000000001e00000000", hexnat% "400000000000000070060000000000", hexnat% "38000000000000000000000", 545357767376896, 2237163114896293888]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204000c204002010000000080000000", hexnat% "40800700000000000000000", hexnat% "20408000000000002000000000000000", hexnat% "3b018000000000000000000", hexnat% "1d80000000072000000000000", 562812514467840, 2273192040764276736]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00290.record002
