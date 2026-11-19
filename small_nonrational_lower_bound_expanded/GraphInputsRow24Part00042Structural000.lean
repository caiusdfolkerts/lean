module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00042Data
public import GraphInputsRow24Part00042Frames
public import GraphInputsRow24Part00042Leaves
public import GraphInputsRow24Part00042Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 17293822569102704640, (certNat% 3), 594475425690812416, 36082131922845696]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), (certNat% 5), 8070450532247928832, (certNat% 6), 6047313952768, 81909218222800896]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 774619135907725312, 81082385478713344, 35184372088832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 16140901064562966528, (certNat% 11), 362924736512, 150633093005312, 166633186212708352]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 9), 891712726219358208, 216383888346316800]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 17293822569102704640, (certNat% 3), 720576215257186304, 288442650615349248]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 8873402433536, 17293822569102704640, (certNat% 3), 94008244174848, 175921860444160]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 8070450532247928832, (certNat% 6)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), 145241517479428096, (certNat% 20), (certNat% 21), 27021599911706624]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 5), 19394461696, 1649267441664, 8070450532247928832, (certNat% 6)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17872825432487755776, (certNat% 23), (certNat% 3), 94008244174848, 166809108073152512, 405886916416765952, 371514671104]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019
def vertexColumn : Fields := ⟨10, (certNat% 24)⟩
def kindColumn : Fields := ⟨3, (certNat% 25)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 38843551081037824, (certNat% 27), 360289138420744192, (certNat% 28), 2147483648]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 158331285012480, (certNat% 30), 225180256246431744, (certNat% 31), 36028865738440704]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 182466153652682752, 72057594037927936, (certNat% 33)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 33), (certNat% 28), 1724034232352768, 182466153652682752, 81064793292668928]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), 328903510286401536, 72057594037927936, (certNat% 33)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 2882303761517117440, (certNat% 33), (certNat% 37)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), 6917529027641081856, (certNat% 40), (certNat% 41), 328903510286401536]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c6
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c5
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), 55009941127168, 146367262767448064, (certNat% 44), (certNat% 39)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 33), (certNat% 37), 2977477488017408]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 2314850208468434944, 2973079441506304, (certNat% 47), 1161084278931456]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), 2977477488017408, 576462951326679040, (certNat% 33), 1161084278931456]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), (certNat% 53), 90073401296683008, 1161101458800640]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 288372762907508736, (certNat% 55), 1691083243257856, (certNat% 56), (certNat% 57)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61), 1741626418397184, 470766898548572160, 72058968427462656]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c22 c11
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c23 c10
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c24 c4
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c26 c0
  c27
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023
def vertexColumn : Fields := ⟨10, (certNat% 62)⟩
def kindColumn : Fields := ⟨3, (certNat% 63)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 105604655874048, (certNat% 65), (certNat% 66), (certNat% 67)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [50665399234068480, (certNat% 68), (certNat% 69), 96502546432, (certNat% 70)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 72), (certNat% 73), (certNat% 74), 89120571392, (certNat% 75)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [50487649730822144, (certNat% 68), (certNat% 70), 177846005792768, (certNat% 69)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 68), (certNat% 77), (certNat% 78), 62277025792, (certNat% 79)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 81), (certNat% 73), 179495273234432, (certNat% 82)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 36301600456704, 50111346242486272, 174348828672, 354317622050816]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 85), 49829866970808320, (certNat% 86), 178120883699712]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), 141906256330752, 50111346242486272, 174214610944, 354317622050816]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 89), (certNat% 90), 49539771994734592, 363113715073024, 176007759790080, 2432696320]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c16 c1
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record027
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b49b19ab19c6a9a662d98e5386e2785ef06b19a599b15c5a9665a56352d58d9354d8b46d2745db0dc3a8e6364cb362d2b1ad1b26c5ba1d8791d4731e2729c6715d0f23c3c5283a258361382e079490e68591625254351342d0758350c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d34926db4d249349249a6d2492492492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 68)]))
 (.leaf ([(facetIndex 50), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 51), (facetIndex 70)]))
 (.leaf ([(facetIndex 76), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 78), (facetIndex 83)]))
 (.leaf ([(facetIndex 79), (facetIndex 84)])))
 (.branch 7
 (.leaf ([(facetIndex 53), (facetIndex 66), (facetIndex 71)]))
 (.leaf ([(facetIndex 80), (facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "58ffb03000c8818000000003044z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record027" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record027" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record027" "{\"ridges\":[[12,386],[18,545],[18,548],[20,641],[36,545],[36,548],[40,386],[41,641],[47,386],[49,386],[50,610],[51,674],[52,386],[57,545],[57,548],[60,396],[62,545],[62,548],[63,641],[64,545],[64,548],[65,545],[65,548],[65,644],[67,641],[68,408],[69,616],[70,688],[71,960],[78,610],[79,674],[83,616],[84,688]],\"owners\":[[12,386,[76,80,82],[40,47,49,52]],[40,386,[82],[12,47,49,52,76,80]],[47,386,[80],[12,40,49,52,76,82]],[49,386,[76,80],[12,40,47,52,82]],[52,386,[76,82],[12,40,47,49,80]],[18,545,[50,51,69,70],[36,57,62,64,65]],[36,545,[69,70],[18,50,51,57,62,64,65]],[57,545,[50,51,70],[18,36,62,64,65,69]],[62,545,[50,51,69],[18,36,57,64,65,70]],[64,545,[51,70],[18,36,50,57,62,65,69]],[65,545,[50,69],[18,36,51,57,62,64,70]],[18,548,[78,79,83,84],[36,57,62,64,65]],[36,548,[83,84],[18,57,62,64,65,78,79]],[57,548,[78,79,84],[18,36,62,64,65,83]],[62,548,[78,79,83],[18,36,57,64,65,84]],[64,548,[79,84],[18,36,57,62,65,78,83]],[65,548,[78,83],[18,36,57,62,64,79,84]],[20,641,[51,53,70,71],[41,63,65,67]],[41,641,[70,71],[20,51,53,63,65,67]],[63,641,[51,53,71],[20,41,65,67,70]],[67,641,[51,70],[20,41,53,63,65,71]],[65,644,[81],[20,41,63,67,79,84]],[50,610,[78],[]],[78,610,[50],[]],[51,674,[79],[]],[79,674,[51],[]],[60,396,[76],[]],[68,408,[82],[]],[69,616,[83],[]],[83,616,[69],[]],[70,688,[84],[]],[84,688,[70],[]],[71,960,[],[]]],\"edges\":[[38,[18,36,50,51,57,62,64,65,69,70,78,79,83,84]],[42,[12,40,47,49,52,60,66,68,71,76,80,82]],[43,[20,41,51,53,63,65,67,70,71,79,81,84]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record027" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record027\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,25,28,30],[-5,30],[-7,28],[-8,25,28],[-11,25,30],[-2,9,10,22,23],[-4,22,23],[-13,9,10,23],[-15,9,10,22],[-17,10,23],[-18,9,22],[-2,26,27,31,32],[-4,31,32],[-13,26,27,32],[-15,26,27,31],[-17,27,32],[-18,26,31],[-3,10,12,23,24],[-6,23,24],[-16,10,12,24],[-20,10,23],[-18,29],[-9,26],[-26,9],[-10,27],[-27,10],[-14,25],[-21,30],[-22,31],[-31,22],[-23,32],[-32,23],[-24],[-9,33],[-22,33],[-10,34],[-23,34],[-25,35],[-30,35],[-26,36],[-31,36],[-27,37],[-32,37],[-12,38],[-19,38],[-28,39],[-29,39],[-33,40],[-34,41],[-34,-35,42],[-41,43],[-42,44],[-40,43],[-37,45],[-36,45],[-39,46],[-38,46],[-45,47],[-45,-46,48],[-43,-48,49],[-44,-47,49],[-49],[2,4,9,10,13,15,17,18,22,23,26,27,31,32],[1,5,7,8,11,14,19,21,24,25,28,30],[3,6,10,12,16,18,20,23,24,27,29,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":386,\"a\":12,\"owners\":[76,80,82]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":386,\"a\":47,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":386,\"a\":49,\"owners\":[76,80]},{\"tag\":\"mate\",\"ridge\":386,\"a\":52,\"owners\":[76,82]},{\"tag\":\"mate\",\"ridge\":545,\"a\":18,\"owners\":[50,51,69,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":36,\"owners\":[69,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":57,\"owners\":[50,51,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":62,\"owners\":[50,51,69]},{\"tag\":\"mate\",\"ridge\":545,\"a\":64,\"owners\":[51,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":65,\"owners\":[50,69]},{\"tag\":\"mate\",\"ridge\":548,\"a\":18,\"owners\":[78,79,83,84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":36,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":57,\"owners\":[78,79,84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":62,\"owners\":[78,79,83]},{\"tag\":\"mate\",\"ridge\":548,\"a\":64,\"owners\":[79,84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":65,\"owners\":[78,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[51,53,70,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":41,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":63,\"owners\":[51,53,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":67,\"owners\":[51,70]},{\"tag\":\"mate\",\"ridge\":644,\"a\":65,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":610,\"a\":50,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":610,\"a\":78,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":674,\"a\":51,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":674,\"a\":79,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":396,\"a\":60,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":408,\"a\":68,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":616,\"a\":69,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":616,\"a\":83,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":688,\"a\":70,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":688,\"a\":84,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":960,\"a\":71,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":50,\"full_literals\":[-9,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-22,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":51,\"full_literals\":[-10,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-23,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-25,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-30,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-26,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-31,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-27,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-32,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-12,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-19,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-28,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":81,\"full_literals\":[-29,39]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[18,36,50,51,57,62,64,65,69,70,78,79,83,84]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,40,47,49,52,60,66,68,71,76,80,82]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,41,51,53,63,65,67,70,71,79,81,84]}]}"
  "66 1 5 7 8 11 14 19 21 25 28 30 0 33 64 0\n67 3 6 10 12 16 18 20 23 27 29 32 0 33 65 0\n68 43 0 51 53 49 48 36 37 34 35 10 26 32 6 8 9 11 24 7 30 63 0\n69 -48 0 68 62 60 0\n70 45 0 54 55 42 43 40 41 16 25 31 12 14 15 17 23 13 29 63 0\n71 47 0 70 58 0\n72 -46 0 70 69 59 0\n73 -44 0 71 62 61 0\n74 -39 0 72 56 0\n75 -38 0 72 57 0\n76 -42 0 73 52 0\n77 -28 0 74 46 0\n78 -29 0 74 47 0\n79 -12 0 75 44 0\n80 -19 0 75 45 0\n81 -7 0 77 3 0\n82 -18 0 78 22 0\n83 35 0 80 81 77 38 39 27 4 2 28 5 1 66 0\n84 -34 0 83 76 50 0\n85 -10 0 84 36 0\n86 -23 0 84 37 0\n87 -20 0 85 86 21 0\n88 -27 0 85 26 0\n89 -3 0 85 79 86 33 18 0\n90 -16 0 85 79 33 20 0\n91 -6 0 86 33 19 0\n92 -32 0 86 32 0\n93 0 90 91 89 85 79 82 87 86 88 78 92 67 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record028
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f0ab29a99ab19c6a9a662d98e5386e2785ef06b19a599b15c5a96652d58d5346d2745de0f43b0dc3a8e63a4d938ccb362e4b8ad2b1ad1b26c5ba1d8791d4731e2729c6715d0f23c3c5283a258361382e079490e4950d44d0b41da0d8390d4388c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db4d249b6db6d3492492492492492492492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 50), (facetIndex 65), (facetIndex 79)]))
 (.leaf ([(facetIndex 31), (facetIndex 43), (facetIndex 49), (facetIndex 61), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 60), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 74), (facetIndex 76), (facetIndex 77)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 34), (facetIndex 36), (facetIndex 51), (facetIndex 54)])))
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 52), (facetIndex 53), (facetIndex 55), (facetIndex 59)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b2c000000048afb6f7fa0c92433fdb51422z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 70)]))
 (.leaf ([(facetIndex 66), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 72)]))
 (.leaf ([(facetIndex 78), (facetIndex 84)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 80), (facetIndex 85)]))
 (.leaf ([(facetIndex 81), (facetIndex 86)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 73)]))
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "f63fec0c003223644z31;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4, 5]
def grouped2_0003 : List Nat := [4, 5, 6, 7]
def grouped2_0004 : List Nat := [6]
def grouped2_0005 : List Nat := [6, 7]
def grouped2_0006 : List Nat := [7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7]
def grouped3_0021 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record028" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record028" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record028" "{\"ridges\":[[11,545],[11,546],[13,577],[36,545],[36,546],[39,577],[40,386],[41,641],[47,545],[47,546],[48,577],[51,545],[51,546],[52,386],[53,641],[54,545],[54,546],[54,578],[55,545],[55,546],[55,642],[57,577],[58,577],[59,386],[66,612],[67,676],[71,616],[72,688],[80,612],[81,676],[85,616],[86,688]],\"owners\":[[11,545,[66,67,71,72],[36,47,51,54,55]],[36,545,[71,72],[11,47,51,54,55,66,67]],[47,545,[66,67,72],[11,36,51,54,55,71]],[51,545,[66,67,71],[11,36,47,54,55,72]],[54,545,[67,72],[11,36,47,51,55,66,71]],[55,545,[66,71],[11,36,47,51,54,67,72]],[11,546,[80,81,85,86],[36,47,51,54,55]],[36,546,[85,86],[11,47,51,54,55,80,81]],[47,546,[80,81,86],[11,36,51,54,55,85]],[51,546,[80,81,85],[11,36,47,54,55,86]],[54,546,[81,86],[11,36,47,51,55,80,85]],[55,546,[80,85],[11,36,47,51,54,81,86]],[13,577,[66,69,71,73],[39,48,54,57,58]],[39,577,[71,73],[13,48,54,57,58,66,69]],[48,577,[66,69,73],[13,39,54,57,58,71]],[57,577,[66,71],[13,39,48,54,58,69,73]],[58,577,[66,69,71],[13,39,48,54,57,73]],[54,578,[83,87],[13,39,48,57,58,80,85]],[40,386,[84,87],[14,49,52,56,59,78,82]],[52,386,[78,82,87],[14,40,49,56,59,84]],[59,386,[78,82,84],[14,40,49,52,56,87]],[41,641,[72,73],[15,53,55,57,59,67,69]],[53,641,[67,69,73],[15,41,55,57,59,72]],[55,642,[83,87],[15,41,53,57,59,81,86]],[66,612,[80],[]],[80,612,[66],[]],[67,676,[81],[]],[81,676,[67],[]],[71,616,[85],[]],[85,616,[71],[]],[72,688,[86],[]],[86,688,[72],[]]],\"edges\":[[38,[11,36,47,51,54,55,66,67,71,72,80,81,85,86]],[41,[13,39,48,54,57,58,66,69,71,73,80,83,85,87]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record028" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record028\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,17,18,20,21],[-3,20,21],[-7,17,18,21],[-9,17,18,20],[-12,18,21],[-13,17,20],[-1,24,25,29,30],[-3,29,30],[-7,24,25,30],[-9,24,25,29],[-12,25,30],[-13,24,29],[-2,17,19,20,22],[-4,20,22],[-8,17,19,22],[-14,17,20],[-15,17,19,20],[-12,27,31],[-5,28,31],[-10,23,26,31],[-16,23,26,28],[-6,21,22],[-11,18,19,22],[-13,27,31],[-17,24],[-24,17],[-18,25],[-25,18],[-20,29],[-29,20],[-21,30],[-30,21],[-32,5,6,10,11,13,16],[-33,32],[-34,33],[-35,34],[35],[-17,36],[-20,36],[-18,37],[-21,37],[-23,38],[-28,38],[-24,39],[-29,39],[-25,40],[-30,40],[-19,41],[-22,41],[-26,42],[-27,42],[-31,42],[-36,43],[-38,44],[-37,44],[-44,45],[-43,45],[-43,-44,46],[-40,47],[-39,47],[-42,48],[-41,48],[-47,49],[-47,-48,50],[-45,-50,51],[-46,-49,51],[-51],[1,3,7,9,12,13,17,18,20,21,24,25,29,30],[2,4,8,12,14,15,17,19,20,22,24,27,29,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":545,\"a\":11,\"owners\":[66,67,71,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":36,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":47,\"owners\":[66,67,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[66,67,71]},{\"tag\":\"mate\",\"ridge\":545,\"a\":54,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":545,\"a\":55,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":546,\"a\":11,\"owners\":[80,81,85,86]},{\"tag\":\"mate\",\"ridge\":546,\"a\":36,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":546,\"a\":47,\"owners\":[80,81,86]},{\"tag\":\"mate\",\"ridge\":546,\"a\":51,\"owners\":[80,81,85]},{\"tag\":\"mate\",\"ridge\":546,\"a\":54,\"owners\":[81,86]},{\"tag\":\"mate\",\"ridge\":546,\"a\":55,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":13,\"owners\":[66,69,71,73]},{\"tag\":\"mate\",\"ridge\":577,\"a\":39,\"owners\":[71,73]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[66,69,73]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[66,69,71]},{\"tag\":\"mate\",\"ridge\":578,\"a\":54,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":386,\"a\":52,\"owners\":[78,82,87]},{\"tag\":\"mate\",\"ridge\":386,\"a\":59,\"owners\":[78,82,84]},{\"tag\":\"mate\",\"ridge\":641,\"a\":41,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[67,69,73]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[83,87]},{\"tag\":\"mate\",\"ridge\":612,\"a\":66,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":612,\"a\":80,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":676,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":676,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":616,\"a\":71,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":616,\"a\":85,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":688,\"a\":72,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":688,\"a\":86,\"owners\":[72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[40,41,52,53,55,59],\"full_literals\":[-32,5,6,10,11,13,16]},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-17,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-20,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-18,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-21,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-24,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-29,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-25,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-30,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":69,\"full_literals\":[-19,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-22,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-26,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-27,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-31,42]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-45,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[11,36,47,51,54,55,66,67,71,72,80,81,85,86]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,39,48,54,57,58,66,69,71,73,80,83,85,87]}]}"
  "70 34 0 37 36 0\n71 33 0 70 35 0\n72 32 0 71 34 0\n73 45 0 56 57 55 53 40 41 38 39 5 28 32 1 3 4 6 26 2 30 68 0\n74 -50 0 73 67 65 0\n75 47 0 59 60 46 47 44 45 11 27 31 7 9 10 12 25 8 29 68 0\n76 49 0 75 63 0\n77 -48 0 75 74 64 0\n78 -46 0 76 67 66 0\n79 -42 0 77 61 0\n80 -41 0 77 62 0\n81 -26 0 79 50 0\n82 -27 0 79 51 0\n83 -31 0 79 52 0\n84 -19 0 80 48 0\n85 -22 0 80 49 0\n86 -12 0 82 83 18 0\n87 -13 0 82 83 24 0\n88 44 0 81 83 84 85 87 72 54 55 42 43 40 41 20 21 19 23 22 33 0\n89 -43 0 88 78 58 0\n90 -36 0 89 53 0\n91 -17 0 90 38 0\n92 -20 0 90 39 0\n93 -14 0 91 92 16 0\n94 -24 0 91 26 0\n95 -2 0 91 84 92 85 13 0\n96 -8 0 91 84 85 15 0\n97 -15 0 91 84 92 17 0\n98 -29 0 92 30 0\n99 -4 0 92 85 14 0\n100 0 96 95 99 86 93 97 91 84 92 85 94 82 98 83 69 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record028
