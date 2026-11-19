module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00037Data
public import GraphInputsRow24Part00037Frames
public import GraphInputsRow24Part00037Leaves
public import GraphInputsRow24Part00037Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), 9022592417529856, (certNat% 18)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 3461017138267947008, (certNat% 21), 9018194371018752]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 3461017138267947008, (certNat% 24), 9020393394274304]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 5), (certNat% 27), (certNat% 24)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 30), 9009673155903488, 3461016863390040064]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 17), (certNat% 33), 9013796324507648, (certNat% 34)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38), 7009386627072, (certNat% 39)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), 9022626777268224, 1081004716776751104, (certNat% 42), (certNat% 43)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4089127715574120448, 522558294263332864, (certNat% 43), (certNat% 44), (certNat% 45), (certNat% 18)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 2891310960771858432, 5910974510923776, 2611340115968, (certNat% 47), (certNat% 48)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), 8143257993216, (certNat% 43), (certNat% 47), (certNat% 48)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3458762709934276608, 1152922191801614336, (certNat% 50), (certNat% 45), (certNat% 23), (certNat% 4)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 53), (certNat% 54), (certNat% 55)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), 1116892707587883008, (certNat% 57), (certNat% 5), (certNat% 58), (certNat% 4)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 11), (certNat% 60), 1116892707587883008]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), (certNat% 5), 8303511812964352, 1116892707587883008, 3458764513820540928]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), (certNat% 20), 1116892707587883008]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 41), (certNat% 4), 8303511812964352, 1116892707587883008, 3458764513820540928]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), 7421703487488, 8303511812964352, 3314649325744685056, 1152921504606846976]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 70), 4505798650626048, 1156580679304085504, 3350818860252004352]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), 504403158265495552, (certNat% 72), (certNat% 73), (certNat% 43), (certNat% 74)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 76), (certNat% 77), 8303511812964352, 3314649325744685056, 1152921504606846976]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 79), 1155454779397242880, (certNat% 80)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), (certNat% 17), (certNat% 82), (certNat% 60), 4505798650626048]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 7177611906121728, 2053641430080946176, (certNat% 84), 2302102470656, (certNat% 52)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), (certNat% 60), (certNat% 87), (certNat% 88), 2199023255552]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 21), (certNat% 90), 1156580679304085504, 4503599627370496]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 92), (certNat% 93), (certNat% 94), (certNat% 95), (certNat% 43)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), 4925812092436480, (certNat% 60), (certNat% 52), (certNat% 20), 1008806316530991104]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), (certNat% 77), 3799912185593856, 432345564227567616]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 5), (certNat% 95), 3799912185593856, (certNat% 4), 1116892707587883008]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 84), (certNat% 60), (certNat% 88), 7177611906121728, 1116892776307359744, (certNat% 43)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c49 c44
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c50 c43
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c51 c42
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c52 c41
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c53 c40
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c54 c35
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c55 c34
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c56 c33
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c57 c32
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c58 c31
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c59 c28
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c60 c25
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c61 c22
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c62 c21
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c63 c20
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c64 c19
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c65 c18
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c66 c17
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c67 c16
  c68
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record009
