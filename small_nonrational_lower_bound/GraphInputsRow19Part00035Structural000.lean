module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00035Data
public import GraphInputsRow19Part00035Frames
public import GraphInputsRow19Part00035Leaves
public import GraphInputsRow19Part00035Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record063
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 7881299347898368, (certNat% 3), 68720001024, 788529152]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4972045332961296384, 1125968911532032, 6755399442104320, (certNat% 4), 4432540467200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4972045401945014272, (certNat% 5), 4432540467200, 2251799818928128, 5629499534213120]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [360363747360636928, 4611686087146864640, 7881299347898368, (certNat% 4)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 1125968626319360, 2322168557862912, 4503599627370496]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 72061992084439040, (certNat% 8), 288300744895889408]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 6755399441055744, (certNat% 10), 360287970189639680]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 893353197568, 2322168557862912, 76565591711809536, 288230376151711744]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 288300744895889408, 369098752, 4611686087146864640]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 962072674304, 2322168557862912, 360287970189639680]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 234881024, 687194767360, 6755399441055744]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 234881024, 4611756387171565568, 1030792151040, 2251799813685248]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 288300744895889408, 72062035034112000, 2251799852482560, 4503599761588224]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 288300744895889408, 3377699720527872, (certNat% 3), 117440512]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 360287978779574272, (certNat% 8), 2322168562057216, 962072674304]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 8), 288300744895889408, 1005022347264, 72057594037927936]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 4611756387171565568, 8594128896, 360287970189639680, 996432412672]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 288230651029618688, 4611686018427387904, 721554505728]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 76561193665298432, (certNat% 3), 84934656, 1005022347264, 288230376151711744]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c29 c20
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c30 c19
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c31 c18
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c32 c11
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c33 c2
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c34 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00035.record063
