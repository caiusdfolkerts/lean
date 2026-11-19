module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00029Data
public import GraphInputsRow16Part00029Frames
public import GraphInputsRow16Part00029Leaves
public import GraphInputsRow16Part00029Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2568459162484736, 180143985094819840, (certNat% 4), 17867063951360]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16254561396195328, 1689468335554560, 270215977642229760, (certNat% 5), (certNat% 6), 70368744177664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 55566139392, 3802111208849408, 43980465111040]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 6), 53085795778560, 1692698687832064, 281474976710656]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 5), 54043195528445952, (certNat% 12)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 288230513590665216, 5067649092419584, 143486267424768, 17592186044416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 36310546873581568, (certNat% 17), 19791209299968]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), 51539607552, (certNat% 21)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 30786325577728, (certNat% 17), 11258999068426240, 432345564227567616, (certNat% 23)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 88046829568, 9429411719806976, 288230376151711744, 34359738368]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 88046829568, 11399736556781568, 288230376151711744, 34359738368]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 88046829568, (certNat% 27), 11681211533492224, 34359738368, 486388759756013568]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13591217178673152, (certNat% 28), 563035852767232, 486388759823122432, (certNat% 8), 3802111208849408, 57483842289664]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008
def vertexColumn : Fields := ⟨10, (certNat% 29)⟩
def kindColumn : Fields := ⟨3, (certNat% 30)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), 63050394783186944, (certNat% 33), 42331197669376]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 2269667146072064, 162129586585337856, (certNat% 36), 68719476736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 343597383680, 45035996273704960, 144124121607831552, 1165482325442560]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 343597383680, (certNat% 39), (certNat% 40), 1165482325442560]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 1165483399184384, (certNat% 42), (certNat% 43), (certNat% 44), 68987912192]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 162129586585337856, (certNat% 36), (certNat% 46), 240518168576, (certNat% 47)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 144124121607831552, 615726511554560, (certNat% 49), 2252143411068928, 5915372557434880]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 577094071001022464, 5910974510923776, (certNat% 51), 52776558133248]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 51), (certNat% 53), 52776558133248, 5915372557434880, 27021597764222976]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 63050394783186944, (certNat% 55), 7107243161944064, (certNat% 56), 277025390592]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), 5985775661350912, (certNat% 59), (certNat% 60), 2269392268165120, 18014398509481984]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032
def vertexColumn : Fields := ⟨10, (certNat% 61)⟩
def kindColumn : Fields := ⟨3, (certNat% 62)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 123147449794560, 74309393851613184, (certNat% 64), 6917529027641081856]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 15942918602752, (certNat% 66), 4683743612465315840, 2305983746702049280, 17179869184]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [280315016773632, (certNat% 67), (certNat% 68), 6917529027641081856, 20266198625157120, 72057619807731712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 70), 24769798218973184, 5260204364768739328, 110226040684544, 2305993092550885376, 26893877248]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record032
