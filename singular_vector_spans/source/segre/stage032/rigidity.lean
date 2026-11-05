module
public import SegreVerified.Stage004
import all Lean.Util.CollectAxioms

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators TensorProduct

section SegreRigidityPrincipal

/-!
# Polynomial-open forms of the complete chain-graph classification

The constructive graph predicates are connected here to nonempty polynomial
opens of actual placements. The stress-free certificate includes both a full
edge-row minor and an affine-frame minor, uniformly in the characteristic.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.RigidityPrincipal

open Matrix RigidityRank GenericRigidity Staircase RankParameters

variable {K I V : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype V]

/-- A stress-free spanning placement supplies a nonzero polynomial certificate
for spanning and stress-freeness of every placement in its nonvanishing locus. -/
theorem stressFree_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : StressFree.GenericallyStressFree K I G) :
    ∃ f : MvPolynomial (V × I) K, f ≠ 0 ∧
      ∀ q : Matrix V I K, MvPolynomial.eval (flattenVelocity q) f ≠ 0 →
        affineSpan K (Set.range q) = ⊤ ∧
          2 * (rigidityMatrix q (endpoints G)).rank = Fintype.card (Edges G) := by
  classical
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  obtain ⟨p₀, hp₀, hpRank⟩ := hG
  let e : V ↪ V := Function.Embedding.refl V
  have he (p : Matrix V I K) : Matrix.of (fun v => p (e v)) = p := rfl
  let ρ := (rigidityMatrix p₀ (endpoints G)).rank
  let R := rigidityMatrix (restrictedUniversal (K := K) (I := I) e) (endpoints G)
  let A := restrictedAugmented (K := K) (I := I) e
  have hR : ρ ≤ (R.map (MvPolynomial.eval (flattenVelocity p₀))).rank := by
    rw [show R = rigidityMatrix (restrictedUniversal (K := K) (I := I) e)
      (endpoints G) from rfl, eval_restrictedRigidity, he p₀] <;> exact le_rfl
  have hA : Fintype.card (Option I) ≤
      (A.map (MvPolynomial.eval (flattenVelocity p₀))).rank := by
    rw [show A = restrictedAugmented (K := K) (I := I) e from rfl,
      eval_restrictedAugmented, he p₀,
      Matrix.vecMul_surjective_iff_rank_eq_card.mp
        (augmented_surjective_of_affineSpan p₀ hp₀)] <;> exact le_rfl
  obtain ⟨r, hr, hwr⟩ := GenericRank.minor_witness R (flattenVelocity p₀) ρ hR
  obtain ⟨a, ha, hwa⟩ := GenericRank.minor_witness A (flattenVelocity p₀)
    (Fintype.card (Option I)) hA
  refine ⟨r * a, mul_ne_zero hr ha, ?_⟩
  intro q hq
  rw [map_mul] at hq
  have hqr := hwr (flattenVelocity q) (mul_ne_zero_iff.mp hq).1
  have hqa := hwa (flattenVelocity q) (mul_ne_zero_iff.mp hq).2
  rw [show R = rigidityMatrix (restrictedUniversal (K := K) (I := I) e)
    (endpoints G) from rfl, eval_restrictedRigidity, he q] at hqr
  rw [show A = restrictedAugmented (K := K) (I := I) e from rfl,
    eval_restrictedAugmented, he q] at hqa
  have hspan : affineSpan K (Set.range q) = ⊤ := by
    apply affineSpan_of_augmented_surjective
    apply Matrix.vecMul_surjective_iff_rank_eq_card.mpr
    exact le_antisymm (Matrix.rank_le_card_width _) hqa
  refine ⟨hspan, ?_⟩
  have hrow := Matrix.rank_le_card_height
    (rigidityMatrix q (StressFree.endpointsOnce G))
  rw [StressFree.rank_edgesOnce G q] at hrow
  have hcard := StressFree.card_oriented_edges G
  dsimp only [ρ] at hqr
  omega

/-- Over an infinite field, the witnessed predicate is exactly its
polynomial-open formulation, including the affine-spanning convention. -/
theorem genericallyStressFree_iff_polynomial_certificate [Infinite K]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    StressFree.GenericallyStressFree K I G ↔
      ∃ f : MvPolynomial (V × I) K, f ≠ 0 ∧
        ∀ p : Matrix V I K, MvPolynomial.eval (flattenVelocity p) f ≠ 0 →
          affineSpan K (Set.range p) = ⊤ ∧
            2 * (rigidityMatrix p (endpoints G)).rank = Fintype.card (Edges G) := by
  constructor
  · exact stressFree_certificate G
  · rintro ⟨f, hf, hw⟩
    obtain ⟨z, hz⟩ := GenericMatrixRank.exists_eval_ne_zero f hf
    let p : Matrix V I K := Matrix.of (flattenVelocity.symm z)
    have hp : flattenVelocity p = z := rfl
    have h := hw p (by rw [hp]; exact hz)
    exact ⟨p, h.1, h.2⟩

/-- The ordinary Maxwell edge deficit rules out every spanning rigid
placement. The factor two counts edge orientations in the natural numbers. -/
theorem not_genericallyRigid_of_edge_deficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdef : Fintype.card (Edges G) <
      2 * (Fintype.card V * Fintype.card I - (Fintype.card I + 1).choose 2)) :
    ¬ GenericallyRigid K I G := by
  classical
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  rintro ⟨p, hspan, hr⟩
  have hrow := Matrix.rank_le_card_height
    (rigidityMatrix p (StressFree.endpointsOnce G))
  rw [StressFree.rank_edgesOnce G p] at hrow
  have hcard := StressFree.card_oriented_edges G
  have hupper : 2 * (rigidityMatrix p (endpoints G)).rank ≤
      Fintype.card (Edges G) := by omega
  rw [rigidityMatrix_rank, rigidity_rank_of_rigid G p hspan hr] at hupper
  exact (not_le_of_gt hdef) hupper

/-- The three fixed cardinality inequalities are checked by the kernel. -/
theorem shape111_not_genericallyRigid :
    ¬ GenericallyRigid K (Fin (sideSum ThreeChainCores.shape111 + 1))
      (chainGraph ThreeChainCores.shape111) := by
  apply not_genericallyRigid_of_edge_deficit
  decide

theorem shape112_not_genericallyRigid :
    ¬ GenericallyRigid K (Fin (sideSum ThreeChainCores.shape112 + 1))
      (chainGraph ThreeChainCores.shape112) := by
  apply not_genericallyRigid_of_edge_deficit
  decide

theorem shape113_not_genericallyRigid :
    ¬ GenericallyRigid K (Fin (sideSum ThreeChainCores.shape113 + 1))
      (chainGraph ThreeChainCores.shape113) := by
  apply not_genericallyRigid_of_edge_deficit
  decide

/-- The obstruction is invariant under every permutation of the factors. -/
theorem not_genericallyRigid_of_exceptional_reindex
    (n : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3))
    (he : (fun i => n (e i)) = ThreeChainCores.shape111 ∨
      (fun i => n (e i)) = ThreeChainCores.shape112 ∨
      (fun i => n (e i)) = ThreeChainCores.shape113) :
    ¬ GenericallyRigid K (Fin (sideSum n + 1)) (chainGraph n) := by
  intro hG
  let m : Fin 3 → ℕ := fun i => n (e i)
  have hm : sideSum m = sideSum n := ChainClassification.sideSum_reindex n e
  have hG' : GenericallyRigid K (Fin (sideSum n + 1)) (chainGraph m) :=
    ChainInduction.orderIso_rigid (ChainClassification.reindexCell n e).symm hG
  let P : (Fin 3 → ℕ) → Prop := fun b =>
    GenericallyRigid K (Fin (sideSum b + 1)) (chainGraph b)
  have hG'' : P m :=
    Eq.mp (congrArg (fun d : ℕ =>
      GenericallyRigid K (Fin (d + 1)) (chainGraph m)) hm.symm) hG'
  rcases he with h111 | h112 | h113
  · exact shape111_not_genericallyRigid (K := K)
      (Eq.mp (congrArg P (show m = ThreeChainCores.shape111 from h111)) hG'')
  · exact shape112_not_genericallyRigid (K := K)
      (Eq.mp (congrArg P (show m = ThreeChainCores.shape112 from h112)) hG'')
  · exact shape113_not_genericallyRigid (K := K)
      (Eq.mp (congrArg P (show m = ThreeChainCores.shape113 from h113)) hG'')

theorem exceptional_not_genericallyRigid (n : Fin 3 → ℕ)
    (hex : ChainClassification.ExceptionalTriple n) :
    ¬ GenericallyRigid K (Fin (sideSum n + 1)) (chainGraph n) := by
  obtain ⟨e, he⟩ := hex
  exact not_genericallyRigid_of_exceptional_reindex n e he

/-- Proposition 5.1, the nonexceptional case, on an explicitly nonempty open
of all actual placements, with no bound on the positive chain lengths. -/
theorem proposition_5_1_rigid [Infinite K] (k : ℕ) (hk : 3 ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (hex : ∀ h : k = 3,
      ¬ ChainClassification.ExceptionalTriple (fun i => n (Fin.cast h.symm i))) :
    ∃ f : MvPolynomial (Cell n × Fin (sideSum n + 1)) K, f ≠ 0 ∧
      (∃ p : Matrix (Cell n) (Fin (sideSum n + 1)) K,
        MvPolynomial.eval (flattenVelocity p) f ≠ 0) ∧
      ∀ p : Matrix (Cell n) (Fin (sideSum n + 1)) K,
        MvPolynomial.eval (flattenVelocity p) f ≠ 0 →
          affineSpan K (Set.range p) = ⊤ ∧
            InfinitesimallyRigidOn (chainGraph n) p Set.univ := by
  obtain ⟨f, hf, hw⟩ := rigidity_certificate (K := K)
    (I := Fin (sideSum n + 1)) (chainGraph n) (Function.Embedding.refl (Cell n))
    (ChainClassification.positive_nonexceptional k hk n hpos hex)
  obtain ⟨z, hz⟩ := GenericMatrixRank.exists_eval_ne_zero f hf
  refine ⟨f, hf, ⟨Matrix.of (flattenVelocity.symm z), ?_⟩, ?_⟩
  · exact hz
  · exact hw

/-- Proposition 5.1, all three exceptional triples and every factor order,
on an explicitly nonempty open of actual stress-free placements. -/
theorem proposition_5_1_stress_free [Infinite K] (n : Fin 3 → ℕ)
    (hex : ChainClassification.ExceptionalTriple n) :
    ∃ f : MvPolynomial (Cell n × Fin (sideSum n + 1)) K, f ≠ 0 ∧
      (∃ p : Matrix (Cell n) (Fin (sideSum n + 1)) K,
        MvPolynomial.eval (flattenVelocity p) f ≠ 0) ∧
      ∀ p : Matrix (Cell n) (Fin (sideSum n + 1)) K,
        MvPolynomial.eval (flattenVelocity p) f ≠ 0 →
          affineSpan K (Set.range p) = ⊤ ∧
            2 * (rigidityMatrix p (endpoints (chainGraph n))).rank =
              Fintype.card (Edges (chainGraph n)) ∧
              ¬ InfinitesimallyRigidOn (chainGraph n) p Set.univ := by
  obtain ⟨f, hf, hw⟩ := stressFree_certificate (K := K)
    (I := Fin (sideSum n + 1)) (chainGraph n)
    (ChainClassification.exceptional_stressFree n hex)
  obtain ⟨z, hz⟩ := GenericMatrixRank.exists_eval_ne_zero f hf
  refine ⟨f, hf, ⟨Matrix.of (flattenVelocity.symm z), ?_⟩, ?_⟩
  · exact hz
  · intro p hp
    obtain ⟨hspan, hrank⟩ := hw p hp
    refine ⟨hspan, hrank, ?_⟩
    intro hrigid
    exact exceptional_not_genericallyRigid n hex ⟨p, hspan, hrigid⟩

end PaperVerification.Segre.RigidityPrincipal

end SegreRigidityPrincipal

end
end

/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
