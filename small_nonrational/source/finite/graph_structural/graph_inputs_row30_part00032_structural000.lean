module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00032Data
public import GraphInputsRow30Part00032Frames
public import GraphInputsRow30Part00032Leaves
public import GraphInputsRow30Part00032Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00032.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014
def vertexColumn : Fields := ⟨10, hexnat% "3c2e8b62e4b52ccaca72aaa6aa6a5aa9a66a5a56a3a4eac671aa669a6659a9665a5655a364d8ce2b86e2785ef07a1d8791d4731b25c9aa5a99a569a6599965598e539b15c5a95a599565a5595955558d535334ad1b49d17783d0ec370f23a8da398d63c4e9364e5354e334ce8b62e4b52ccb8ad2b2ac6b86d1b26c5b0ee8761e4751cc789d2729c6785d1725c570dc8f13c2f07c3c8c9320e8362384e0b81e8c5310e4352344d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d36db6db6936db6db6924926db69b6db6db49b6db6db4924936db6db6db6936db6db6db4db6db6db6d2491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨35, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨129, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e00000000001e0000", hexnat% "400c00c00006000800200000", hexnat% "1f0000000000000000000000000", hexnat% "200600600000000000000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00032.record014
