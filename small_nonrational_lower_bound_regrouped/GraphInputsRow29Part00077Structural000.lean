module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00077Data
public import GraphInputsRow29Part00077Frames
public import GraphInputsRow29Part00077Leaves
public import GraphInputsRow29Part00077Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2251902892900352, (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 4755801206503243776, 1568669696, (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 3), 2264993953218560, (certNat% 11), (certNat% 12), (certNat% 6)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 1956642816, (certNat% 14), 2265097032433664, 212755499974656, (certNat% 15), (certNat% 16)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022
def vertexColumn : Fields := ⟨10, (certNat% 17)⟩
def kindColumn : Fields := ⟨3, (certNat% 18)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 17884512256000, 35769024512000, 144115188075855872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 2251800082120704]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 25)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨8, by decide⟩ c1 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c1 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c2 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c6 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 25), (certNat% 28)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 35218731827200, (certNat% 25)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 25), (certNat% 28), 35768487641088]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 28), (certNat% 32), 275146342400, 35769024512000]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 35769024512000, (certNat% 34), (certNat% 35), 2392812448382976, (certNat% 36)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), (certNat% 34), (certNat% 45)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 43), (certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 35), (certNat% 21), (certNat% 52), 1161686111223808, 4503599627370496]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 21), 35769024512000, 288371116055986176, (certNat% 54), (certNat% 55)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 21), (certNat% 58), 1143510078062592, 35768487641088]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 35), (certNat% 60), 108086391124000768, 1179261117399040, 4503599627370496]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 34), (certNat% 62), 17609433022464, 1125900712148992, 35768487641088]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 48), (certNat% 62), (certNat% 49), (certNat% 64), 1143510078062592, 35768487641088]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c37 c32
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c38 c31
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c39 c30
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c40 c29
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c41 c26
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c42 c25
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c43 c0
  c44
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record022
