module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00034Data
public import GraphInputsRow26Part00034Frames
public import GraphInputsRow26Part00034Leaves
public import GraphInputsRow26Part00034Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00034.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1143630068711424, 6917529028983259136, 846623953387520, (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 17729641775104, (certNat% 5), (certNat% 3), (certNat% 6)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 1147890139398144, (certNat% 8), (certNat% 9), (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 844424930131968, 6917529027641081856, (certNat% 6)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 281474976710656, (certNat% 13), (certNat% 6)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 1143492092887040, 281474976710656]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 144132780261900288, 2306124484190404608, 1688849860263936]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 281474976710656, (certNat% 13), (certNat% 17)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 2306124484190404608, (certNat% 13), (certNat% 17), 1688849860263936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 2306124484190404608, 13853072453791645696, 1691048883519488]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 2306124484190404608, (certNat% 22), 13853072453791645696, 1691048883519488]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 16158915463005339648, (certNat% 24), (certNat% 6), 144115188075855872]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 2323857407995805696, (certNat% 6), (certNat% 27)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 144132918254501888, 846624226017280, 16158915463005339648, (certNat% 3)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c23 c2
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00034.record014
