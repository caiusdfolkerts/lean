module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00000Data
public import GraphInputsRow25Part00000Frames
public import GraphInputsRow25Part00000Leaves
public import GraphInputsRow25Part00000Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record057
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057
def vertexColumn : Fields := ⟨10, hexnat% "398e5274e316cc729c673c29cb8aa68bae1b4699a9695a361db0ea398e5386e8789ef07915a5992e785d1565c5695656551d58d5352d1b51d27783d0ec370e9394cb31cd8b52cab1af07a1d8791d4785c9715d0f23c4fd103ca489a0ea4619a160d82e0798926439514650d50d0b41d18c930cc8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db49a4924db6926da4d26db4924936da6926936d2492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b82030800603fc0000000", hexnat% "4000280020000000000", hexnat% "8401000001000000000000", hexnat% "4000080000040000000000", 387309567953862656, hexnat% "100000100000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44011805605607c0000000", hexnat% "280000800200000000000", hexnat% "8000000001000000000000", hexnat% "10280001000000000", hexnat% "1000020000002000000000", hexnat% "102000000000800000000", hexnat% "804000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c503080421640ec0000000", hexnat% "4000280020000000000", hexnat% "100000100000000000", hexnat% "30000003000000000", hexnat% "280000800000000000000", 90071996842377216, hexnat% "1800000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8703030fe1003fc0000000", hexnat% "884000000000000000000", hexnat% "1000000000100000000000", hexnat% "4000080000440000000000", 37383395344384, hexnat% "100000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c703090421440e80000000", hexnat% "1000020000003000000000", hexnat% "100000100000000000", hexnat% "80000800200000000000", 270215983010938880, hexnat% "804000000000000000000", 2199023255552]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c040303c0063fc0000000", hexnat% "280000800200000000000", hexnat% "100420100000000000", hexnat% "103000000000000000000", hexnat% "c000000001400000000000", hexnat% "80000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f86000a80222ec0000000", hexnat% "20001000000000000", hexnat% "c001000000000000000000", hexnat% "10000001000000000", hexnat% "80000440000000000", hexnat% "100420100000000000", 90071996842377216]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000000006606c0000000", hexnat% "c003000000000000000000", hexnat% "10980000000000000", hexnat% "180020100000000000", hexnat% "984000000000000000000", hexnat% "1000020000003000000000", 281509336449024, 450359967032016896]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00000.record057_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00000.record057
