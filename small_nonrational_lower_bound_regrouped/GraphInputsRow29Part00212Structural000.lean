module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00212Data
public import GraphInputsRow29Part00212Frames
public import GraphInputsRow29Part00212Leaves
public import GraphInputsRow29Part00212Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00212.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 2748779069440, (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 7), (certNat% 12), (certNat% 9), 4123571257344, (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 8796093022208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), 13510919141195776, (certNat% 20), 2886352240640]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 216173056991690752, (certNat% 22), (certNat% 23)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27), 144176760727011328, (certNat% 28)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 216173881625411584, (certNat% 22), (certNat% 23)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 25), (certNat% 31), (certNat% 32), 72119166689083392, (certNat% 33)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), 2748779069440, (certNat% 5)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 12), 1374389534720, (certNat% 38), (certNat% 39)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 12), (certNat% 42), (certNat% 38), 4260741775360]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 18), 3161364365312, (certNat% 45)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50), 2886620676096]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 53), 216174156503318528, (certNat% 22), (certNat% 23)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 36), 2748779069440, (certNat% 5)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 8), (certNat% 58), (certNat% 39)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), (certNat% 61), (certNat% 58), 4260875993088, (certNat% 62)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 25), (certNat% 64), (certNat% 65), 216209340875407360, (certNat% 23)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 49), (certNat% 67), (certNat% 23), (certNat% 52), (certNat% 50)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 49), (certNat% 23), (certNat% 52), (certNat% 50)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 47), (certNat% 52), 2886620676096, (certNat% 49), (certNat% 50)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), 105553653137408, (certNat% 19), (certNat% 72), 2893063127040, (certNat% 53), (certNat% 73)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c34 c29
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c35 c28
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c36 c27
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c37 c22
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c38 c21
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c39 c18
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c40 c13
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c41 c10
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c42 c7
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c43 c4
  c44
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00212.record002
