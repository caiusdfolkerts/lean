module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00019Data
public import GraphInputsRow26Part00019Frames
public import GraphInputsRow26Part00019Leaves
public import GraphInputsRow26Part00019Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00019.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011
def vertexColumn : Fields := ⟨10, hexnat% "3b03e0f4cb0ec370bc1f3326c8f2729aa3a8da2e87ac9a361d92e1b85e0fba1e4731ac5b1727296a4d92e725954d58d4b5c34cd8b52d2b49d1743d70f2368f1364cd38cd332cd8b52ccb4acab26c5b0ef0789d2785c3743c2f07da88d12a158361382e34589326151544d14d0b12c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db69b6da4924db6d349b49369b6d36db69b6924da6db492449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182c44204710280000", 45035996286287872, hexnat% "600000000000100000", hexnat% "1800000000000000000", hexnat% "40000000000080000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f80820000290f80000", hexnat% "40000000004500000000", 54078379900534784, 2595199285272248320]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f804a0200010d80000", 27919384576, 19140298416324608, hexnat% "40000000004100000000", 2882303761517117440]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18800e0204010d80000", hexnat% "100400000000000000", 2306968922005438464, hexnat% "40000800000480000000", hexnat% "600000000000200000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "680080000010300000", hexnat% "1000020000000c00000", 306280233911189504, 2306968922005438464, hexnat% "40000800000480000000", hexnat% "900000000000080000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00019.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00019.record011
