module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00042Data
public import GraphInputsRow29Part00042Frames
public import GraphInputsRow29Part00042Leaves
public import GraphInputsRow29Part00042Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00042.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008
def vertexColumn : Fields := ⟨10, hexnat% "15c2f07ce4b8a6695a3693a2e87ad1aa6c5a96558b61db0ea394e2b86e4789e1783ee478966559365392e479d16a5c5695554b51d70da354d2b46d4749d1743de0f43a8f13a4d9334d331cf0ba2d8b32d2b1ad1b26c5b0ef07a1e4751e2729c6785d1725e0f43c8f07d522c94a2a8560d84e0b9512c5492a4550d44d0b703a0d4328d1324c530cd0b22c4b0ae0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69b4db6d24da49b49b69b4db6d24da49b492492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48294c48290e7e07fffe00000000", 9286422431637962752, hexnat% "10110000000000000", hexnat% "c00008000000000000", hexnat% "10800010000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4818cc48188e7e07fffe00000000", 9286422431637962752, hexnat% "10110000000000000", hexnat% "1400008000000000000", hexnat% "21000020000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48290c48294e7e07fffe00000000", 9286422431637962752, hexnat% "10110000000000000", hexnat% "10800010800000000000000000", hexnat% "400000000008000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48188c4818ce7e07fffe00000000", 9286422431637962752, hexnat% "10110000000000000", hexnat% "21000021000000000000000000", hexnat% "400000000008000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84c00084e7e087ffe00000000", hexnat% "10800010800000800000000000", hexnat% "21000021000001000000000000", 139611588448485376, hexnat% "800000800008002000000000000", hexnat% "4000004000010004000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40298c002187fffffffe00000000", hexnat% "400008400000000000000000", hexnat% "10000010000000000000000000", hexnat% "800004800080000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2084000087fffffffe00000000", hexnat% "10000010000000000000000000", hexnat% "1000021000000000000000000", hexnat% "8400008400000000000000000", hexnat% "4800084800080000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4829cc4801cd45ff9f9e00000000", hexnat% "10000010000000202000000000", hexnat% "2a000400000000000", hexnat% "28000200004000000000", 1729382256910270464]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2088002083fffffefe00000000", hexnat% "1000001000000000000000000", hexnat% "10000010000000000000000000", hexnat% "8400008400000010000000000", hexnat% "48000448000c0000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88000083fdff869e00000000", hexnat% "10000010000000202000000000", hexnat% "8400008400200010000000000", 97031901151232, hexnat% "48000448000c0000000000000000", hexnat% "21000021000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40314c003107fffffffe00000000", hexnat% "800000800000000000000000", hexnat% "8000008400000000000000000", hexnat% "800004800080000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1104001007fffffffe00000000", hexnat% "800000800000000000000000", hexnat% "20000021000000000000000000", hexnat% "8400008400000000000000000", hexnat% "4800084800080000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1100001103fffffefe00000000", hexnat% "800000800000000000000000", hexnat% "20000020000000000000000000", hexnat% "8400008400000010000000000", hexnat% "48000c48000c0000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000001003fff786e200000000", hexnat% "800000800000200400000000", hexnat% "8400008400008010000000000", hexnat% "21000021000000480800000000", hexnat% "48000c48000c0000000000000000", 17660905521152]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1080001080041022a400000000", hexnat% "21000021000000484800000000", hexnat% "8400008400208010200000000", hexnat% "35144000000000000", 12151274744599019520, hexnat% "48000c48000c0001800000000000", 22058952032256]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c26 c17
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c27 c8
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00042.record008
