module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00127Data
public import GraphInputsRow24Part00127Frames
public import GraphInputsRow24Part00127Leaves
public import GraphInputsRow24Part00127Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 10133099161583616, 9295429630892703744, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 9223380832947798016, (certNat% 7), 72057594574798848, (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 8830519869440, 4503874505277440, 153122387330596864, 703687441776640]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 6), (certNat% 11), 103079215104, 712483534798848]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 712483534798848, 157625986974744576, (certNat% 13), 120259084288, 100663296]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 16888498602639360, (certNat% 6), 576495945265446912, (certNat% 8), (certNat% 15)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 173388585653764096, (certNat% 17), 9511602413006487552, (certNat% 7), 35184372088832]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 120795955200, 173388585653764096, (certNat% 19), (certNat% 20), 1125899906842624]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨8, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨12, by decide⟩ c12 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c11 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 162129586585337856]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 563224831328256, 162129586585337856, 9223372036854775808]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 162129586585337856, (certNat% 25), 9799832789158199296, (certNat% 11)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 6), (certNat% 27), 562949953421312, (certNat% 28)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 571748193927168, 450359962737049600, (certNat% 30), 576495971035250688, (certNat% 31)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 9223372036854775808, (certNat% 22), 563224831328256]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 563224831328256, 9799832789158199296, (certNat% 31), (certNat% 25)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 9511602413006487552, (certNat% 6), 562952100904960, 144115188075855872]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), 432345566375051264, 571746046443520, (certNat% 7), 9223372036854775808]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 571746046443520, 13510798882111488, (certNat% 6)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 9223380832947798016, 157625986957967360, (certNat% 6), 562952100904960]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), 153122387330596864, (certNat% 3), 571748193927168, 9511602413006487552]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 157625986957967360, 9223380832947798016, (certNat% 41), 563226978811904, 288230376151711744]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c43 c40
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), 171136785840078848, (certNat% 15), 9799867973530288128, 288230376151711744]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 159877786771652608, 9529616811515969536, (certNat% 45), (certNat% 46), 44015361720320, (certNat% 47)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c48 c37
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c49 c26
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c50 c10
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c51 c9
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c52 c8
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c53 c7
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c54 c2
  c55
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record000
