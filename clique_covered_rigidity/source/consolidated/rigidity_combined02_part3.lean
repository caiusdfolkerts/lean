module
public import consolidated.rigidity_combined02_part2
import all consolidated.rigidity_combined02_part2
set_option Elab.async false
section BundleSource0052
/- Source: Papers/RigidityZheng_NullCellule_ProvenanceFlagGroundedPF.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ProvenanceFlagGroundedPF.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
The rooted semismallness proof and its complete supporting lemmas are retained.
The unrelated final zero-defect body-pin corollary is omitted from this extraction.
-/






@[expose] public section

/-!
# From provenance-flag semismallness to grounded PF

The provenance-flag theorem is naturally ungrounded: its empty-flag
specialization has ambient dimension `3 * |V|`.  The selected-null height
assembly needs the corresponding root-zero estimate with ambient dimension
`3 * (|V| - 1)`.

This file proves the exact bridge.  Starting with a root-zero placement over
`K`, it adjoins three independent common-translation variables.  Common
translation leaves every direction row, hence the stress space, unchanged,
while the function-field transcendence degree increases by exactly three.
Applying empty-flag semismallness upstairs and cancelling those three
dimensions gives the grounded estimate.
-/

namespace RB31E2E

noncomputable section

namespace ProvenanceFlagGroundedPF

open ProvenanceFlag

/-! ## Three independent common translations -/

abbrev TranslationRing (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

abbrev TranslationField (K : Type*) [Field K] :=
  FractionRing (TranslationRing K)

def translationCoordinate {K : Type*} [Field K] (j : Fin 3) :
    TranslationField K :=
  algebraMap (TranslationRing K) (TranslationField K) (MvPolynomial.X j)

def translatedPlacement
    {K V : Type*} [Field K]
    (a : V → Fin 3 → K) : V → Fin 3 → TranslationField K :=
  fun v j ↦ algebraMap K (TranslationField K) (a v j) +
    translationCoordinate j

theorem translatedPlacement_root
    {K V : Type*} [Field K] {a : V → Fin 3 → K} {root : V}
    (hroot : a root = 0) (j : Fin 3) :
    translatedPlacement a root j = translationCoordinate j := by
  simp [translatedPlacement, hroot]

theorem translatedPlacement_injective
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (ha : Function.Injective a) :
    Function.Injective (translatedPlacement a) := by
  intro u v huv
  apply ha
  funext j
  have hj := congrFun huv j
  simp only [translatedPlacement] at hj
  have : algebraMap K (TranslationField K) (a u j) =
      algebraMap K (TranslationField K) (a v j) := by
    exact add_right_cancel hj
  exact (RingHom.injective (algebraMap K (TranslationField K))) this

theorem directionRow_translatedPlacement
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (e : SimpleEdge V) :
    DirectionStress.directionRow (translatedPlacement a) e =
      DirectionStress.directionRow
        (DirectionStress.mapPlacement (K := TranslationField K) a) e := by
  funext v j
  simp only [DirectionStress.directionRow, DirectionStress.edgeDirection,
    translatedPlacement, DirectionStress.mapPlacement]
  split_ifs <;> ring

theorem directionStressDim_translatedPlacement
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) (a : V → Fin 3 → K) :
    DirectionStress.directionStressDim F (translatedPlacement a) =
      DirectionStress.directionStressDim F a := by
  have hmap :
      DirectionStress.directionEquilibrium F (translatedPlacement a) =
        DirectionStress.directionEquilibrium F
          (DirectionStress.mapPlacement (K := TranslationField K) a) := by
    apply LinearMap.ext
    intro weight
    funext v j
    simp only [DirectionStress.directionEquilibrium_apply,
      DirectionStress.directionEquilibriumCoordinate]
    apply Finset.sum_congr rfl
    intro e _he
    rw [directionRow_translatedPlacement a e.1]
  calc
    DirectionStress.directionStressDim F (translatedPlacement a) =
        DirectionStress.directionStressDim F
          (DirectionStress.mapPlacement (K := TranslationField K) a) := by
      unfold DirectionStress.directionStressDim
      change Module.finrank (TranslationField K)
          (LinearMap.ker
            (DirectionStress.directionEquilibrium F (translatedPlacement a))) =
        Module.finrank (TranslationField K)
          (LinearMap.ker
            (DirectionStress.directionEquilibrium F
              (DirectionStress.mapPlacement
                (K := TranslationField K) a)))
      rw [hmap]
    _ = DirectionStress.directionStressDim F a :=
      DirectionStress.directionStressDim_mapPlacement F a

/-! ## The translation field has relative transcendence degree three -/

theorem adjoin_translationCoordinate_eq_top
    {K : Type*} [Field K] :
    IntermediateField.adjoin K (Set.range (translationCoordinate (K := K))) =
      ⊤ := by
  let A : IntermediateField K (TranslationField K) :=
    IntermediateField.adjoin K
      (Set.range (translationCoordinate (K := K)))
  have hX (j : Fin 3) : translationCoordinate (K := K) j ∈ A :=
    IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  have hpoly : ∀ p : TranslationRing K,
      algebraMap (TranslationRing K) (TranslationField K) p ∈ A := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        simpa [A, IsScalarTower.algebraMap_apply K
          (TranslationRing K) (TranslationField K)] using
          A.algebraMap_mem c
    | add p q hp hq =>
        simpa using A.add_mem hp hq
    | mul_X p j hp =>
        simpa [map_mul, translationCoordinate] using A.mul_mem hp (hX j)
  apply top_unique
  intro z _hz
  obtain ⟨p, q, _hq, rfl⟩ :=
    IsFractionRing.div_surjective (TranslationRing K) z
  exact A.div_mem (hpoly p) (hpoly q)

theorem translationCoordinate_isTranscendenceBasis
    {K : Type*} [Field K] :
    IsTranscendenceBasis K (translationCoordinate (K := K)) := by
  let R := TranslationRing K
  let L := TranslationField K
  have hInjective : Function.Injective
      (algebraMap R L) := IsFractionRing.injective R L
  have hIndependent : AlgebraicIndependent K
      (translationCoordinate (K := K)) := by
    have hX := MvPolynomial.algebraicIndependent_X (Fin 3) K
    have hmap := hX.map
      (f := IsScalarTower.toAlgHom K R L)
      hInjective.injOn
    change AlgebraicIndependent K
      (fun j : Fin 3 => algebraMap R L (MvPolynomial.X j))
    exact hmap
  have hField : Algebra.IsAlgebraic
      (IntermediateField.adjoin K
        (Set.range (translationCoordinate (K := K)))) L :=
    ⟨fun z ↦ by
      have hz : z ∈ IntermediateField.adjoin K
          (Set.range (translationCoordinate (K := K))) := by
        rw [adjoin_translationCoordinate_eq_top]
        exact trivial
      have hmap : algebraMap
          (IntermediateField.adjoin K
            (Set.range (translationCoordinate (K := K)))) L
          (⟨z, hz⟩ : IntermediateField.adjoin K
            (Set.range (translationCoordinate (K := K)))) = z := rfl
      rw [← hmap]
      exact isAlgebraic_algebraMap _⟩
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hIndependent, ?_⟩
  exact (IntermediateField.isAlgebraic_adjoin_iff_top).mp hField

theorem trdeg_translationField
    {K : Type*} [Field K] :
    Algebra.trdeg K (TranslationField K) = 3 := by
  simpa using
    (translationCoordinate_isTranscendenceBasis
      (K := K)).lift_cardinalMk_eq_trdeg.symm

theorem trdeg_translationField_over_base
    {k K : Type*} [Field k] [Field K] [Algebra k K] :
    Algebra.trdeg k (TranslationField K) = Algebra.trdeg k K + 3 := by
  calc
    Algebra.trdeg k (TranslationField K) =
        Algebra.trdeg k K + Algebra.trdeg K (TranslationField K) :=
      (trdeg_add_eq k K).symm
    _ = Algebra.trdeg k K + 3 := by rw [trdeg_translationField]

/-! ## The translated placement still generates the whole field -/

theorem translatedPlacement_generated
    {k K V : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype V] [DecidableEq V]
    (a : V → Fin 3 → K) (root : V)
    (hroot : a root = 0)
    (hgen : IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤) :
    IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦
        translatedPlacement a x.1 x.2)) = ⊤ := by
  let A : IntermediateField k (TranslationField K) :=
    IntermediateField.adjoin k
      (Set.range (fun x : V × Fin 3 ↦
        translatedPlacement a x.1 x.2))
  have htranslated (v : V) (j : Fin 3) :
      translatedPlacement a v j ∈ A :=
    IntermediateField.subset_adjoin k _ ⟨⟨v, j⟩, rfl⟩
  have htranslation (j : Fin 3) :
      translationCoordinate (K := K) j ∈ A := by
    rw [← translatedPlacement_root hroot j]
    exact htranslated root j
  have hcoordinate (v : V) (j : Fin 3) :
      algebraMap K (TranslationField K) (a v j) ∈ A := by
    have hsub := A.sub_mem (htranslated v j) (htranslation j)
    simpa [translatedPlacement] using hsub
  have hbase (x : K) : algebraMap K (TranslationField K) x ∈ A := by
    have hx : x ∈ IntermediateField.adjoin k
        (Set.range (fun y : V × Fin 3 ↦ a y.1 y.2)) := by
      rw [hgen]
      exact trivial
    exact IntermediateField.adjoin_induction k
      (motive := fun y _hy ↦ algebraMap K (TranslationField K) y ∈ A)
      (fun y hy ↦ by
        obtain ⟨⟨v, j⟩, rfl⟩ := hy
        exact hcoordinate v j)
      (fun c ↦ by
        simpa [IsScalarTower.algebraMap_apply k K (TranslationField K)] using
          A.algebraMap_mem c)
      (fun _ _ _ _ hy hz ↦ by simpa using A.add_mem hy hz)
      (fun _ _ hy ↦ by simpa using A.inv_mem hy)
      (fun _ _ _ _ hy hz ↦ by simpa using A.mul_mem hy hz)
      hx
  have hpoly : ∀ p : TranslationRing K,
      algebraMap (TranslationRing K) (TranslationField K) p ∈ A := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        simpa [IsScalarTower.algebraMap_apply K
          (TranslationRing K) (TranslationField K)] using hbase c
    | add p q hp hq =>
        simpa using A.add_mem hp hq
    | mul_X p j hp =>
        simpa [map_mul, translationCoordinate] using
          A.mul_mem hp (htranslation j)
  apply top_unique
  intro z _hz
  obtain ⟨p, q, _hq, rfl⟩ :=
    IsFractionRing.div_surjective (TranslationRing K) z
  exact A.div_mem (hpoly p) (hpoly q)

/-! ## Empty flags and completion sparsity -/

def emptyFlagState {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) : ProvenanceFlag.State V (Fin 0) where
  edges := F
  terminals := Fin.elim0
  missing := Fin.elim0
  terminals_card := fun t ↦ Fin.elim0 t
  missing_supported := fun t ↦ Fin.elim0 t
  missing_not_live := fun t ↦ Fin.elim0 t
  other_terminal_edges_live := fun t ↦ Fin.elim0 t

theorem emptyFlagState_completionEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) :
    (emptyFlagState F).completionEdges =
      (emptyFlagState F).liftedLiveEdges := by
  simp [ProvenanceFlag.State.completionEdges,
    ProvenanceFlag.State.restoredMissingEdges,
    ProvenanceFlag.State.ghostStarEdges]

theorem map_drop_liftLiveEdge
    {V : Type*} [DecidableEq V] (e : SimpleEdge V) :
    Sparse22Transport.mapSimpleEdge
        (Equiv.sumEmpty V (Fin 0)).toEmbedding
        (ProvenanceFlag.liftLiveEdge (Flag := Fin 0) e) = e := by
  apply Subtype.ext
  simp [Sparse22Transport.mapSimpleEdge,
    ProvenanceFlag.liftLiveEdge, Sym2.map_map, Function.comp_def]

theorem emptyFlagState_completionSparse
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleEdgeSet V) (hF : Sparse22 F) :
    (emptyFlagState F).CompletionSparse := by
  rw [ProvenanceFlag.State.CompletionSparse,
    emptyFlagState_completionEdges]
  apply Sparse22Transport.sparse22_of_mapEdgeSet_subset
    (Equiv.sumEmpty V (Fin 0)).toEmbedding hF
  intro e he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hg
  change Sparse22Transport.mapSimpleEdge
      (Equiv.sumEmpty V (Fin 0)).toEmbedding
      (ProvenanceFlag.liftLiveEdge (Flag := Fin 0) f) ∈ F
  rw [map_drop_liftLiveEdge]
  exact hf

/-! ## Passage to the grounded inequality -/

/-- Empty-flag semismallness implies the rooted direction-stress inequality.
Grounding and all cardinal conversions are proved in this declaration. -/
theorem groundedPF_of_provenanceFlag_semismallness
    (hFlagPF :
      ∀ {k K V Flag : Type}
        [Field k] [Field K] [Algebra k K]
        [Fintype V] [DecidableEq V]
        [Fintype Flag] [DecidableEq Flag]
        (S : ProvenanceFlag.State V Flag),
        S.CompletionSparse →
        ∀ Y : ProvenanceFlag.FunctionFieldBranch (k := k) (K := K) S,
          Y.SemismallBudget S) :
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (F : SimpleEdgeSet V), Sparse22 F →
      ∀ (root : V) {K : Type} [Field K] [Algebra ℚ K]
        (a : V → Fin 3 → K),
        a root = 0 →
        Function.Injective a →
        IntermediateField.adjoin ℚ
            (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
        DirectionStress.directionStressDim F a +
            (Algebra.trdeg ℚ K).toNat ≤
          Nat.card (GroundedTwistSplit.SpatialVariable root) := by
  intro V _instFV _instDV F hSparse root K _instFieldK _instAlgQK
    a hroot hinjective hgenerated
  let S := emptyFlagState F
  let Y : ProvenanceFlag.FunctionFieldBranch
      (k := ℚ) (K := TranslationField K) S := {
    position := translatedPlacement a
    generated := translatedPlacement_generated a root hroot hgenerated
    distinct := translatedPlacement_injective a hinjective
    collinear := fun t ↦ Fin.elim0 t
  }
  have hBudget := hFlagPF S (emptyFlagState_completionSparse F hSparse) Y
  have hEmptyBudget :
      (Y.stressDim S : Cardinal) +
          Algebra.trdeg ℚ (TranslationField K) ≤
        3 * (Fintype.card V : Cardinal) :=
    (Y.semismallBudget_of_flag_card_zero_iff S (by simp)).mp hBudget
  change
      (DirectionStress.directionStressDim F (translatedPlacement a) : Cardinal) +
          Algebra.trdeg ℚ (TranslationField K) ≤
        3 * (Fintype.card V : Cardinal) at hEmptyBudget
  rw [directionStressDim_translatedPlacement,
    trdeg_translationField_over_base] at hEmptyBudget
  have hTrdegFinite : Algebra.trdeg ℚ K < Cardinal.aleph0 :=
    (FiniteCoordinateTrdeg.trdeg_le_three_mul_card
      (fun x : V × Fin 3 ↦ a x.1 x.2) hgenerated).trans_lt
        (Cardinal.mul_lt_aleph0
          Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0)
  have hRightFinite :
      3 * (Fintype.card V : Cardinal) < Cardinal.aleph0 :=
    Cardinal.mul_lt_aleph0
      Cardinal.natCast_lt_aleph0 Cardinal.natCast_lt_aleph0
  have hNat := Cardinal.toNat_le_toNat hEmptyBudget hRightFinite
  have hStressFinite :
      (DirectionStress.directionStressDim F a : Cardinal) <
        Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  have hThreeFinite : (3 : Cardinal) < Cardinal.aleph0 := by simp
  rw [Cardinal.toNat_add hStressFinite
      (Cardinal.add_lt_aleph0 hTrdegFinite hThreeFinite),
    Cardinal.toNat_add hTrdegFinite hThreeFinite] at hNat
  simp at hNat
  have hOffRoot :
      Fintype.card (OffRoot root) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun v : V ↦ v = root)]
    simp
  rw [Nat.card_eq_fintype_card]
  simp only [GroundedTwistSplit.SpatialVariable,
    Fintype.card_prod, Fintype.card_fin, hOffRoot]
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  omega

end ProvenanceFlagGroundedPF

end

end RB31E2E


end
end BundleSource0052

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0052/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0052.json"

section BundleSource0053
/- Source: Papers/RigidityNullHeight.lean -/





@[expose] public section

/-!
# Sparse null-difference height, with all semismallness inputs discharged

The source is Dongzhe Zheng's Apache-2.0 formalization at commit
`e457fde9100c9b7226bd4d81af6860f210a531ab`. The imported files retain their
provenance. This wrapper removes the auxiliary semismallness premise from
the exact minimal-prime height theorem, using its proved source theorem.

The ideal is the actual polynomial ideal generated by
`(ω_i - ω_j) · (t_i - t_j)`. The nonvanishing denominator chooses, for every
pair of distinct body labels, an actual nonzero difference coordinate.
Consequently the theorem concerns the full distinct-twist locus, not a
condition that encodes the desired codimension conclusion.
-/

namespace Papers.Rigidity.NullHeight

open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.PinOuterActiveHeight
open RB31E2E.PinOuterFullProvenanceHeightTransfer
open RB31E2E.SelectedNullHeight
open RB31E2E.UniversalHomogeneousChart

/-- Each irreducible component of the sparse null-difference equations
meeting the specified distinct-point chart has codimension exactly the
number of selected simple edges. There is no semismallness or height
hypothesis in this statement. -/
theorem coefficientMinimalPrime_height_eq_edgeCard
    {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P) :
    P.height = (F.card : ℕ∞) := by
  apply WittShearDistinctPrime.coefficientMinimalPrime_height_eq_edgeCard_of_groundedPF
    root src dst active hLoop F hRepresented chart P hP hden
  exact ProvenanceFlagGroundedPF.groundedPF_of_provenanceFlag_semismallness
    ProvenanceFlag.provenanceFlag_semismallness V F hSparse root

theorem coefficientMinimalPrime_height_ge_edgeCard
    {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (chart : DistinctnessChart V)
    (P : Ideal (TwistCoefficientRing root)) [P.IsPrime]
    (hP : P ∈ (coefficientSelectedNullIdeal root src dst active
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented)).minimalPrimes)
    (hden : coefficientDistinctnessDenominator root chart ∉ P) :
    (F.card : ℕ∞) ≤ P.height :=
  (coefficientMinimalPrime_height_eq_edgeCard
    root src dst active hLoop F hSparse hRepresented chart P hP hden).symm.le

end Papers.Rigidity.NullHeight

end
end BundleSource0053

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0053/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0053.json"

section BundleSource0054
/- Source: Papers/RigidityZheng_NullCellule_SelectedNullHeightPrimewise.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/SelectedNullHeightPrimewise.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Primewise selected-null height

Localization and spectator-variable transport convert a direct height theorem
for surviving coefficient minimal primes into the required selected-null
height bound.  The resulting theorem assumes only grounded collinearity-flag
semismallness.
-/

namespace RB31E2E

namespace SelectedNullHeightPrimewise

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open MvPolynomial
open GroundedTwistPolynomial
open PinOuterActiveHeight
open PinOuterFullProvenanceHeightTransfer
open PolynomialPrimeTrdegHeight
open UniversalHomogeneousChart
open SelectedNullHeight

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- A lower-height theorem for all surviving coefficient minimal primes
implies the terminal function-field inequality by the finite polynomial-prime
dimension formula. -/
theorem survivingSelectedFunctionFieldBudget_of_primewiseHeight
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hHeight : ∀ (P : Ideal (TwistCoefficientRing root)),
      P ∈ (coefficientSelectedNullIdeal
        root src dst active selected).minimalPrimes →
      activeAngularDenominator root src dst active angularChart ∉ P →
      coefficientDistinctnessDenominator root distinctChart ∉ P →
      (selected.card : ℕ∞) ≤ P.height) :
    SurvivingSelectedFunctionFieldBudget
      root src dst active angularChart selected distinctChart := by
  intro P hP hAngular hDistinct
  letI : P.IsPrime := hP.1.1
  let t := (Algebra.trdeg ℚ
    (FractionRing (TwistCoefficientRing root ⧸ P))).toNat
  have hformula := polynomialPrime_height_add_fractionTrdeg_eq_natCard P
  have hadd : (selected.card : ℕ∞) + (t : ℕ∞) ≤
      (Nat.card (GroundedTwistVariable root) : ℕ∞) := by
    calc
      (selected.card : ℕ∞) + (t : ℕ∞) ≤
          P.height + (t : ℕ∞) :=
        by simpa [add_comm] using
          (add_le_add_right (hHeight P hP hAngular hDistinct) (t : ℕ∞))
      _ = (Nat.card (GroundedTwistVariable root) : ℕ∞) := hformula
  have hn : t + selected.card ≤ Nat.card (GroundedTwistVariable root) := by
    apply ENat.coe_le_coe.mp
    simpa only [Nat.cast_add, add_comm] using hadd
  simpa [t, add_comm] using hn

/-- Public localization/spectator bridge whose input is direct primewise
height, not a full-twist function-field budget. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_primewiseHeight
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hHeight : ∀ (P : Ideal (TwistCoefficientRing root)),
      P ∈ (coefficientSelectedNullIdeal
        root src dst active selected).minimalPrimes →
      activeAngularDenominator root src dst active angularChart ∉ P →
      coefficientDistinctnessDenominator root distinctChart ∉ P →
      (selected.card : ℕ∞) ≤ P.height) :
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  exact incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_budget
    root src dst active hLoop angularChart selected distinctChart
      (survivingSelectedFunctionFieldBudget_of_primewiseHeight
        root src dst active angularChart selected distinctChart hHeight)

/-- The selected-null localized lower-height bound required by the incidence
transfer follows directly from grounded PF semismallness.  No
`SurvivingSelectedFunctionFieldBudget`, selected-null height, or generic
fibre identity is a premise. -/
theorem incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_groundedPF
    {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (angularChart : active → Fin 3)
    (distinctChart : DistinctnessChart V)
    (hPF : ∀ {K : Type u} [Field K] [Algebra ℚ K]
      (a : V → Fin 3 → K),
      a root = 0 →
      Function.Injective a →
      IntermediateField.adjoin ℚ
          (Set.range (fun x : V × Fin 3 ↦ a x.1 x.2)) = ⊤ →
      DirectionStress.directionStressDim F a +
          (Algebra.trdeg ℚ K).toNat ≤
        Nat.card (GroundedTwistSplit.SpatialVariable root)) :
    let selected := SparseNullIncidence.selectedSkeletonOccurrences
      src dst active hLoop F hRepresented
    (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart := by
  classical
  dsimp only
  let selected := SparseNullIncidence.selectedSkeletonOccurrences
    src dst active hLoop F hRepresented
  apply incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_primewiseHeight
    root src dst active hLoop angularChart selected distinctChart
  intro P hP _hAngular hDistinct
  letI : P.IsPrime := hP.1.1
  have hF :=
    WittShearDistinctPrime.coefficientMinimalPrime_height_eq_edgeCard_of_groundedPF
      root src dst active hLoop F hRepresented distinctChart P hP hDistinct hPF
  rw [SparseNullIncidence.card_selectedSkeletonOccurrences
    src dst active hLoop F hRepresented]
  exact hF.symm.le

end

end SelectedNullHeightPrimewise

end RB31E2E


end
end BundleSource0054

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0054/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0054.json"

section BundleSource0055
/- Source: Papers/RigidityQuantitativeHeight.lean -/





@[expose] public section

/-!
# The quantitative generic incidence height bound

The primewise coordinate-localization argument is adapted from Dongzhe Zheng's
Apache-2.0 `PinOuterFullProvenanceHeightTransfer.lean` at commit
`e457fde9100c9b7226bd4d81af6860f210a531ab`. Its conclusion here retains the
actual number of active pin occurrences and selected sparse null equations,
without specializing to the zero-defect case.

The terminal sparse theorem has no semismallness, codimension, height, or
rigidity hypothesis. Its prime is an ordinary prime over the actual universal
compatibility and selected-null equations, avoiding the literal product of
pairwise-difference and active-angular coordinates. Homogeneity is not needed.
-/

namespace Papers.Rigidity.QuantitativeHeight

noncomputable section

open MvPolynomial
open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.UniversalHomogeneousChart
open RB31E2E.PinTriangularElimination
open RB31E2E.TotalRingProvenanceSwap
open RB31E2E.PinOuterActiveHeight
open RB31E2E.ActivePinPrimeHeight
open RB31E2E.UniversalActivePinHeightTransfer
open RB31E2E.PinOuterFullProvenanceHeightTransfer

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Every prime over the incidence equations pays two height units for each
active occurrence, in addition to the selected-null coefficient height. -/
theorem genericIncidencePrime_height_ge_active_add_selected
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (angularChart : active → Fin 3) (selected : Finset active)
    (distinctChart : DistinctnessChart V)
    (hselected : (selected.card : ℕ∞) ≤
      incidenceLocalizedSelectedNullIdealHeight
        root src dst active angularChart selected distinctChart) :
    ∀ (Q : Ideal (FiniteGenericRelativeRing root E)), Q.IsPrime →
      finiteGenericUniversalChartIdeal root src dst active angularChart selected ≤ Q →
      finiteGenericIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart ∉ Q →
      ((2 * active.card + selected.card : ℕ) : ℕ∞) ≤ Q.height := by
  intro Q hQprime hchart hdenominator
  letI : Q.IsPrime := hQprime
  let P₀ : Ideal (RelativeRing root E) :=
    Ideal.comap (finiteGenericChartHom root) Q
  letI : P₀.IsPrime := by
    dsimp [P₀]
    exact Ideal.comap_isPrime _ _
  let swap : RelativeRing root E ≃+* PinOuterRing root E :=
    (totalRingSwap (E := E) root).toRingEquiv
  let P₁ : Ideal (PinOuterRing root E) := Ideal.map swap P₀
  letI : P₁.IsPrime := by
    dsimp [P₁]
    exact Ideal.map_isPrime_of_equiv swap
  have hfullP₀ : universalIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ P₀ := by
    simpa [P₀, finiteGenericIncidenceProvenanceDenominator] using
      hdenominator
  have hfullP₁ : C (coefficientIncidenceProvenanceDenominator
      root src dst active distinctChart angularChart) ∉ P₁ := by
    intro hx
    have hback := (Ideal.symm_apply_mem_of_equiv_iff
      (I := P₀) (f := swap)
      (y := C (coefficientIncidenceProvenanceDenominator
        root src dst active distinctChart angularChart))).2 hx
    have hswap :=
      totalRingSwapHom_universalIncidenceProvenanceDenominator
        root src dst active hLoop distinctChart angularChart
    have hinverse : swap.symm
        (C (coefficientIncidenceProvenanceDenominator
          root src dst active distinctChart angularChart)) =
        universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart := by
      rw [← hswap]
      change swap.symm (swap
        (universalIncidenceProvenanceDenominator
          root src dst active hLoop distinctChart angularChart)) = _
      exact swap.symm_apply_apply _
    apply hfullP₀
    simpa [hinverse] using hback
  have hAngular : C (activeAngularDenominator
      root src dst active angularChart) ∉ P₁ :=
    angularDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  have hDistinctSource : C (coefficientDistinctnessDenominator
      root distinctChart) ∉ P₁ :=
    distinctnessDenominator_not_mem_of_incidenceDenominator_not_mem
      root src dst active distinctChart angularChart P₁ hfullP₁
  let P₂ : Ideal (PrivatePresentationRing
      root src dst active angularChart) :=
    Ideal.map
      (localizedSplitPinOuterHom
        root src dst active angularChart) P₁
  letI : P₂.IsPrime := by
    dsimp [P₂]
    exact localizedSplitPinOuterHom_isPrime
      root src dst active angularChart P₁ hAngular
  letI : IsDomain (AngularCoefficientLocalization
      root src dst active angularChart) :=
    angularCoefficientLocalizationIsDomain
      root src dst active angularChart hLoop
  letI : Nontrivial (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : IsDomain (RetainedCoefficientRing
      root src dst active angularChart) := inferInstance
  letI : CommRing (PrivatePresentationRing
      root src dst active angularChart) := inferInstance
  let R := RetainedCoefficientRing
    root src dst active angularChart
  let Cₚ : R →+* PrivatePresentationRing
      root src dst active angularChart := C
  let Pcoeff : Ideal R := Ideal.comap Cₚ P₂
  letI : Pcoeff.IsPrime := by
    dsimp [Pcoeff]
    exact Ideal.comap_isPrime _ _
  have hsource : universalChartIdeal
      root src dst active angularChart selected ≤ P₀ := by
    intro f hf
    change finiteGenericChartHom root f ∈ Q
    exact hchart (Ideal.mem_map_of_mem _ hf)
  have hactiveSource : activeCompatibilityIdeal
      root src dst active angularChart ≤ P₀ :=
    (activeCompatibilityIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have hselectedSource : Ideal.span
      (selectedNullGeneratorSet root src dst active selected) ≤ P₀ :=
    (selectedNullIdeal_le_universalChartIdeal
      root src dst active angularChart selected).trans hsource
  have himage : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart) P₀ = P₂ := by
    dsimp [P₂, P₁]
    rw [localizedPrivatePresentationHom, ← Ideal.map_map]
    rfl
  have hmappedActive : Ideal.map
      (localizedPrivatePresentationHom
        root src dst active angularChart)
      (activeCompatibilityIdeal
        root src dst active angularChart) ≤ P₂ := by
    rw [← himage]
    exact Ideal.map_mono hactiveSource
  have hcompat : localizedActiveCompatibilityIdeal
      root src dst active angularChart ≤ P₂ :=
    (localizedActiveCompatibilityIdeal_le_map_activeCompatibilityIdeal
      root src dst active angularChart).trans hmappedActive
  let Iselected : Ideal R := Ideal.span
    (Set.range (fun e : SelectedOccurrence active selected ↦
      retainedNullEquation
        root src dst active angularChart e.1.1))
  have hretainedSelected : Iselected ≤ Pcoeff := by
    dsimp [Iselected]
    rw [Ideal.span_le]
    rintro _ ⟨e, rfl⟩
    change C (retainedNullEquation
      root src dst active angularChart e.1.1) ∈ P₂
    rw [← localizedPrivatePresentationHom_universalNullEquation
      root src dst active angularChart e.1.1, ← himage]
    exact Ideal.mem_map_of_mem _
      (hselectedSource (Ideal.subset_span ⟨e, rfl⟩))
  have hrelative : Pcoeff.height + (2 * active.card : ℕ) ≤
      P₂.height := by
    simpa [Pcoeff, Cₚ, R] using
      (privatePresentation_prime_height_ge_coefficientContraction_add_twice_card
        root src dst active angularChart hLoop P₂ hcompat)
  have hP₀height : P₀.height = Q.height := by
    exact finiteGenericChartHom_height_comap root Q
  have hP₁height : P₁.height = P₀.height := by
    exact RingEquiv.height_map swap P₀
  have hP₂height : P₂.height = P₁.height := by
    exact localizedSplitPinOuterHom_height_map
      root src dst active angularChart hLoop P₁ hAngular
  have hP₂heightQ : P₂.height = Q.height :=
    hP₂height.trans (hP₁height.trans hP₀height)
  have hDistinctAfterAngular :=
    localizedSplitPinOuterHom_not_mem_map_of_not_mem
      root src dst active angularChart P₁ hAngular
        (C (coefficientDistinctnessDenominator root distinctChart))
        hDistinctSource
  have hretainedDistinct : retainedDistinctnessDenominator
      root src dst active angularChart distinctChart ∉ Pcoeff := by
    intro hx
    apply hDistinctAfterAngular
    change C (retainedDistinctnessDenominator
      root src dst active angularChart distinctChart) ∈ P₂ at hx
    simpa [P₂, retainedDistinctnessDenominator] using hx
  let d : R := retainedDistinctnessDenominator
    root src dst active angularChart distinctChart
  let T := Localization.Away d
  let Pfull : Ideal T := Ideal.map
    (algebraMap R T) Pcoeff
  have hdisjDistinct : Disjoint
      (Submonoid.powers d : Set R)
      (Pcoeff : Set R) :=
    (Ideal.disjoint_powers_iff_notMem
      d
      (Ideal.IsPrime.isRadical inferInstance)).2 hretainedDistinct
  have hPfullHeight : Pfull.height = Pcoeff.height := by
    dsimp [Pfull, T]
    exact IsLocalization.height_map_of_disjoint
      (Submonoid.powers d)
      Pcoeff hdisjDistinct
  let Ifull : Ideal T := Ideal.map (algebraMap R T) Iselected
  have hselectedFull : Ifull ≤ Pfull := by
    dsimp [Ifull, Pfull]
    exact Ideal.map_mono hretainedSelected
  have hselectedHeight : (selected.card : ℕ∞) ≤ Ifull.height := by
    simpa [incidenceLocalizedSelectedNullIdealHeight, R, d, T,
      Iselected, Ifull] using hselected
  have hselectedCoeff : (selected.card : ℕ∞) ≤ Pcoeff.height := by
    calc
      (selected.card : ℕ∞) ≤ Ifull.height := hselectedHeight
      _ ≤ Pfull.height := Ideal.height_mono hselectedFull
      _ = Pcoeff.height := hPfullHeight
  calc
    ((2 * active.card + selected.card : ℕ) : ℕ∞) =
        (selected.card : ℕ∞) + (2 * active.card : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_comm]
    _ ≤ Pcoeff.height + (2 * active.card : ℕ) := by
      exact add_le_add hselectedCoeff le_rfl
    _ ≤ P₂.height := hrelative
    _ = Q.height := hP₂heightQ

/-- The exact quantitative sparse-null incidence bound, with the sparse
codimension input fully discharged by the proven semismallness theorem. -/
theorem genericIncidencePrime_height_ge_active_add_sparse
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f)
    (angularChart : active → Fin 3) (distinctChart : DistinctnessChart V)
    (Q : Ideal (FiniteGenericRelativeRing root E)) [Q.IsPrime]
    (hchart : finiteGenericUniversalChartIdeal root src dst active angularChart
      (SparseNullIncidence.selectedSkeletonOccurrences
        src dst active hLoop F hRepresented) ≤ Q)
    (hdenominator : finiteGenericIncidenceProvenanceDenominator
      root src dst active hLoop distinctChart angularChart ∉ Q) :
    ((2 * active.card + F.card : ℕ) : ℕ∞) ≤ Q.height := by
  have hselected :=
    SelectedNullHeightPrimewise.incidenceLocalizedSelectedNullIdealHeight_ge_selectedCard_of_groundedPF
      root src dst active hLoop F hRepresented angularChart distinctChart
      (ProvenanceFlagGroundedPF.groundedPF_of_provenanceFlag_semismallness
        ProvenanceFlag.provenanceFlag_semismallness V F hSparse root)
  have h := genericIncidencePrime_height_ge_active_add_selected
    root src dst active hLoop angularChart
    (SparseNullIncidence.selectedSkeletonOccurrences
      src dst active hLoop F hRepresented) distinctChart hselected
    Q inferInstance hchart hdenominator
  rw [SparseNullIncidence.card_selectedSkeletonOccurrences
    src dst active hLoop F hRepresented] at h
  exact h

end

end Papers.Rigidity.QuantitativeHeight

end
end BundleSource0055

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0055/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0055.json"

section BundleSource0056
/- Source: Papers/RigidityPairPinSparseRank.lean -/




@[expose] public section

/-!
# Quantitative rank paid by active pins and a sparse null skeleton

This theorem combines the ordinary generic motion ideal, its literal row
rank, the charts supplied by actual separating motions, and the proven
sparse null-height dependency. Its conclusion is about the original
occurrence-level pin matrix.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.UniversalHomogeneousChart

/-- Distinct motion classes pay two independent rank units per active pin
and one more per selected simple `(2,2)`-sparse support edge. -/
theorem genericMotionMatrix_rank_ge_active_add_sparse
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e)
    (hsep : BodiesSeparated src dst)
    (F : SimpleEdgeSet V) (hSparse : Sparse22 F)
    (hRepresented : ∀ f ∈ F, ∃ e : active,
      SparseNullIncidence.activeEdge src dst active hLoop e = f) :
    2 * active.card + F.card ≤ (genericMotionMatrix root src dst).rank := by
  obtain ⟨dc, ac, hden⟩ :=
    exists_finiteIncidenceChart_of_bodiesSeparated root src dst active hLoop hsep
  have h := QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse
    root src dst active hLoop F hSparse hRepresented ac dc
    (finiteMotionIdeal root src dst)
    (finiteChartIdeal_le_finiteMotionIdeal root src dst active ac _) hden
  rw [finiteMotionIdeal_height_eq_rank] at h
  exact_mod_cast h

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0056

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0056/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0056.json"

section BundleSource0057
/- Source: Papers/RigidityDefectRank.lean -/





@[expose] public section

/-!
# The quantitative defect bound for the separated motion quotient

The sparse edge set is chosen from the actual crossing support. Each of
its edges is represented by an original labelled pin, and the active-pin
cardinality equals the original crossing multiplicity sum. The final rank
estimate therefore counts the literal grounded compatibility matrix.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.UniversalHomogeneousChart

/-- Original pin occurrences crossing an arbitrary body labelling. -/
def crossingPinsOn (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) : Finset H.Pin :=
  Finset.univ.filter fun e => label (H.left e) ≠ label (H.right e)

@[simp] theorem mem_crossingPinsOn (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) (e : H.Pin) :
    e ∈ crossingPinsOn H label ↔ label (H.left e) ≠ label (H.right e) := by
  simp [crossingPinsOn]

theorem crossingPinsOn_loopless (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) :
    ∀ e ∈ crossingPinsOn H label, (label ∘ H.left) e ≠ (label ∘ H.right) e := by
  intro e he
  exact (mem_crossingPinsOn H label e).mp he

/-- Counting fibres of the actual unordered endpoint map counts each
crossing occurrence once. -/
theorem card_crossingPinsOn_eq_fineMassOn (H : BodyPinIncidence)
    {I : Type} [Fintype I] [DecidableEq I] (label : H.Body → I) :
    (crossingPinsOn H label).card = H.fineMassOn label := by
  classical
  let pair : H.Pin → Sym2 I := fun e => s(label (H.left e), label (H.right e))
  have hFiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset H.Pin) ((⊤ : SimpleGraph I).edgeFinset) pair
  calc
    (crossingPinsOn H label).card =
        (Finset.univ.filter fun e => pair e ∈ (⊤ : SimpleGraph I).edgeFinset).card := by
      congr 1
      ext e
      simp [crossingPinsOn, pair, SimpleGraph.edgeSet_top, Sym2.mk_isDiag_iff]
    _ = ∑ b ∈ (⊤ : SimpleGraph I).edgeFinset, H.bundleMultiplicityOn label b := by
      rw [← hFiber]
      apply Finset.sum_congr rfl
      intro b hb
      unfold BodyPinIncidence.bundleMultiplicityOn
      congr 1
    _ = ∑ e : SimpleEdge I, H.fineMultiplicityOn label e :=
      sum_completeEdges_eq_sum_simpleEdges _
    _ = H.fineMassOn label := (H.fineMassOn_eq_sum_simpleEdges label).symm

theorem exists_crossingPinOn_activeEdge_eq (H : BodyPinIncidence)
    {I : Type} [Fintype I] [DecidableEq I] (label : H.Body → I)
    (f : SimpleEdge I) (hf : f ∈ H.fineSupportOn label) :
    ∃ e : crossingPinsOn H label,
      SparseNullIncidence.activeEdge (label ∘ H.left) (label ∘ H.right)
        (crossingPinsOn H label) (crossingPinsOn_loopless H label) e = f := by
  classical
  have hpos := (H.mem_fineSupportOn label f).mp hf
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have hpair : s(label (H.left e), label (H.right e)) = f.1 := by
    simpa only [BodyPinIncidence.fineMultiplicityOn,
      BodyPinIncidence.bundleMultiplicityOn, Finset.mem_filter,
      Finset.mem_univ, true_and] using he
  have hcross : e ∈ crossingPinsOn H label := by
    rw [mem_crossingPinsOn]
    intro h
    apply f.2
    rw [← hpair]
    simp [h]
  exact ⟨⟨e, hcross⟩, Subtype.ext hpair⟩

/-- Every partition-defect upper bound controls the full grounded kernel
once identical motion classes have been collapsed. -/
theorem six_mul_pred_le_genericMotionRank_add_defect
    (H : BodyPinIncidence) (D : ℕ) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (ht : 2 ≤ t)
    (hpartition : PartitionDefectAtMost H D)
    (hsep : BodiesSeparated (π ∘ H.left) (π ∘ H.right)) (root : Fin t) :
    6 * (t - 1) ≤ (genericMotionMatrix root (π ∘ H.left) (π ∘ H.right)).rank + D := by
  have hsmall : ∀ e ∈ H.fineSupportOn π, H.fineMultiplicityOn π e ≤ 2 := by
    intro e he
    exact fineMultiplicity_le_two_of_bodiesSeparated H π hsep e
  obtain ⟨F, hFsub, hFsparse, hFcard⟩ :=
    exists_sparse_nullSkeleton_of_defect_bound H D π hπ ht hpartition hsmall
  have hRepresented : ∀ f ∈ F, ∃ e : crossingPinsOn H π,
      SparseNullIncidence.activeEdge (π ∘ H.left) (π ∘ H.right)
        (crossingPinsOn H π) (crossingPinsOn_loopless H π) e = f := by
    intro f hf
    exact exists_crossingPinOn_activeEdge_eq H π f (hFsub hf)
  have hrank := genericMotionMatrix_rank_ge_active_add_sparse root
    (π ∘ H.left) (π ∘ H.right) (crossingPinsOn H π)
    (crossingPinsOn_loopless H π) hsep F hFsparse hRepresented
  rw [card_crossingPinsOn_eq_fineMassOn, hFcard] at hrank
  omega

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0057

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0057/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0057.json"

section BundleSource0058
/- Source: Papers/RigidityGenericDefectBound.lean -/



@[expose] public section

/-!
# Every partition defect bound controls the whole generic motion kernel

All bodies that are identical on the actual generic kernel are collapsed.
The resulting kernel is linearly isomorphic to the original one, its
bodies are separated by genuine motions, and the quantitative incidence
rank theorem applies. This proves the complete upper-bound direction of
the pair-pin defect formula over the independent pin coefficient field.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.GroundedTwistPolynomial
open RB31E2E.UniversalHomogeneousChart
open MotionQuotient

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The full generic compatible-motion kernel modulo common twists is at
most every upper bound for all partition defects. All intermediate
separation and codimension obligations are derived, not assumed. -/
theorem genericGroundedKernel_finrank_le_partitionDefectBound
    (H : BodyPinIncidence) (root : H.Body) (D : ℕ)
    (hpartition : PartitionDefectAtMost H D) :
    Module.finrank (GenericPinCoefficientField H.Pin)
      (groundedPinOperator root H.left H.right genericPins).ker ≤ D := by
  classical
  let K := GenericPinCoefficientField H.Pin
  let p : H.Pin → RB31E2E.Vec3 K := genericPins
  let C := BodyClasses H.left H.right p
  let t : ℕ := Fintype.card C
  let e : C ≃ Fin t := Fintype.equivFin C
  let π : H.Body → Fin t := e ∘ bodyClass H.left H.right p
  have hπ : Function.Surjective π :=
    e.surjective.comp Quotient.mk_surjective
  have hsep : BodiesSeparated (π ∘ H.left) (π ∘ H.right) := by
    intro i j hij
    have hclasses : e.symm i ≠ e.symm j := by
      intro h
      exact hij (e.symm.injective h)
    obtain ⟨X, hX⟩ := distinct_classes_separated H.left H.right p
      (e.symm i) (e.symm j) hclasses
    refine ⟨fun q => X.1 (e.symm q), ?_, hX⟩
    intro a
    have ha := (mem_motionSpace_iff _ _ _ _).mp X.2 a
    simpa [π, classSource, classTarget] using ha
  let qroot : Fin t := π root
  let equivGrounded :
      groundedMotionSpace qroot (π ∘ H.left) (π ∘ H.right) p ≃ₗ[K]
        groundedMotionSpace root H.left H.right p :=
    (groundedReindexEquiv e (bodyClass H.left H.right p root)
      (classSource H.left H.right p) (classTarget H.left H.right p) p).trans
      (groundedClassEquiv root H.left H.right p)
  have hnullity :
      Module.finrank K (groundedPinOperator qroot (π ∘ H.left) (π ∘ H.right) p).ker =
        Module.finrank K (groundedPinOperator root H.left H.right p).ker :=
    (groundedKernelEquiv qroot (π ∘ H.left) (π ∘ H.right) p).finrank_eq.trans
      (equivGrounded.finrank_eq.trans (groundedKernelEquiv root H.left H.right p).finrank_eq.symm)
  have hRN := genericMotion_rank_add_nullity qroot (π ∘ H.left) (π ∘ H.right)
  simp only [Fintype.card_fin] at hRN
  change (genericMotionMatrix qroot (π ∘ H.left) (π ∘ H.right)).rank +
    Module.finrank K (groundedPinOperator qroot (π ∘ H.left) (π ∘ H.right) p).ker =
      6 * (t - 1) at hRN
  rw [hnullity] at hRN
  by_cases ht : 2 ≤ t
  · have hRank := six_mul_pred_le_genericMotionRank_add_defect H D π hπ ht hpartition hsep qroot
    change Module.finrank K (groundedPinOperator root H.left H.right p).ker ≤ D
    omega
  · change Module.finrank K (groundedPinOperator root H.left H.right p).ker ≤ D
    have : t - 1 = 0 := by omega
    rw [this] at hRN
    omega

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0058

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0058/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0058.json"

section BundleSource0059
/- Source: Papers/RigidityZheng_Rigidity_TwistNecessity.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Rigidity/TwistNecessity.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Partition necessity for rigid body--twist systems

For a fixed surjective block labelling, we ground one block and group all
pin constraints by their unordered pair of block labels.  Each grouped
operator factors through one relative six-dimensional twist.  Its signed
pin evaluations have the same kernel as ordinary pin evaluations, so the
proved `0,3,5,6` bundle bounds apply without any rank hypothesis.
-/

namespace RB31E2E

/-- The rank of a finite product of linear maps is at most the sum of the
ranks of its coordinate maps. -/
theorem finrank_range_pi_le_sum
    {k I V : Type*} [Field k] [Fintype I]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : I → Type*} [(i : I) → AddCommGroup (W i)]
    [(i : I) → Module k (W i)]
    (f : (i : I) → V →ₗ[k] W i) :
    Module.finrank k (LinearMap.range (LinearMap.pi f)) ≤
      ∑ i, Module.finrank k (LinearMap.range (f i)) := by
  classical
  let Φ : LinearMap.range (LinearMap.pi f) →ₗ[k]
      ((i : I) → LinearMap.range (f i)) :=
    { toFun := fun y i ↦ ⟨y.1 i, by
        obtain ⟨x, hx⟩ := y.2
        refine ⟨x, ?_⟩
        simpa using congrFun hx i⟩
      map_add' := by
        intro y z
        funext i
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a y
        funext i
        apply Subtype.ext
        rfl }
  have hΦ : Function.Injective Φ := by
    intro y z hyz
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hyz i)
  calc
    Module.finrank k (LinearMap.range (LinearMap.pi f)) ≤
        Module.finrank k ((i : I) → LinearMap.range (f i)) :=
      LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ i, Module.finrank k (LinearMap.range (f i)) := by
      rw [Module.finrank_pi_fintype]

namespace Twist

variable {k I : Type*} [Field k]

/-- The proved bundle bound, transported from `Fin m` to an arbitrary finite
occurrence type without losing occurrence provenance. -/
theorem finrank_range_bundleLinear_le_pinCapacity_card
    [Fintype I] (p : I → Vec3 k) :
    Module.finrank k (LinearMap.range (bundleLinear p)) ≤
      pinCapacity (Fintype.card I) := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let q : Fin (Fintype.card I) → Vec3 k := p ∘ e.symm
  have hker : LinearMap.ker (bundleLinear p) =
      LinearMap.ker (bundleLinear q) := by
    ext X
    constructor
    · intro hX
      rw [LinearMap.mem_ker] at hX ⊢
      funext j
      have hj := congrFun hX (e.symm j)
      simpa [q] using hj
    · intro hX
      rw [LinearMap.mem_ker] at hX ⊢
      funext i
      have hi := congrFun hX (e i)
      simpa [q] using hi
  have hp := (bundleLinear p).finrank_range_add_finrank_ker
  have hq := (bundleLinear q).finrank_range_add_finrank_ker
  rw [hker] at hp
  have hrange : Module.finrank k (LinearMap.range (bundleLinear p)) =
      Module.finrank k (LinearMap.range (bundleLinear q)) := by
    omega
  rw [hrange]
  exact finrank_range_bundleLinear_le_pinCapacity (Fintype.card I) q

/-- Coordinatewise signed evaluation of one relative twist. -/
noncomputable def signedBundleLinear [Fintype I]
    (p : I → Vec3 k) (sign : I → k) :
    Twist k →ₗ[k] (I → Vec3 k) :=
  LinearMap.pi fun i ↦ sign i • evalLinear (p i)

@[simp] theorem signedBundleLinear_apply [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (X : Twist k) (i : I) :
    signedBundleLinear p sign X i = sign i • eval X (p i) := by
  simp [signedBundleLinear]

/-- Nonzero coordinate signs do not change the kernel of bundle evaluation. -/
theorem ker_signedBundleLinear_eq [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (hsign : ∀ i, sign i ≠ 0) :
    LinearMap.ker (signedBundleLinear p sign) =
      LinearMap.ker (bundleLinear p) := by
  ext X
  constructor
  · intro hX
    rw [LinearMap.mem_ker] at hX ⊢
    funext i
    have hi := congrFun hX i
    simp only [signedBundleLinear_apply, Pi.zero_apply] at hi
    exact (smul_eq_zero.mp hi).resolve_left (hsign i)
  · intro hX
    rw [LinearMap.mem_ker] at hX ⊢
    funext i
    have hi := congrFun hX i
    simp only [bundleLinear_apply, Pi.zero_apply] at hi
    simp [signedBundleLinear_apply, hi]

/-- The `0,3,5,6` bound is invariant under independent nonzero signs on the
occurrence coordinates. -/
theorem finrank_range_signedBundleLinear_le_pinCapacity_card [Fintype I]
    (p : I → Vec3 k) (sign : I → k) (hsign : ∀ i, sign i ≠ 0) :
    Module.finrank k (LinearMap.range (signedBundleLinear p sign)) ≤
      pinCapacity (Fintype.card I) := by
  have hker := ker_signedBundleLinear_eq p sign hsign
  have hs := (signedBundleLinear p sign).finrank_range_add_finrank_ker
  have hu := (bundleLinear p).finrank_range_add_finrank_ker
  rw [hker] at hs
  have hrange : Module.finrank k (LinearMap.range (signedBundleLinear p sign)) =
      Module.finrank k (LinearMap.range (bundleLinear p)) := by
    omega
  rw [hrange]
  exact finrank_range_bundleLinear_le_pinCapacity_card p

end Twist

namespace BodyPinIncidence

/-- An unordered pair of distinct labels in a `t`-block partition. -/
abbrev PartitionEdge (t : ℕ) :=
  ↑((⊤ : SimpleGraph (Fin t)).edgeFinset)

/-- The occurrence type of pins belonging to one unordered block bundle. -/
abbrev PartitionBundlePin (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :=
  ↑(Finset.univ.filter fun e : H.Pin ↦
    s(π (H.left e), π (H.right e)) = b.1)

@[simp] theorem card_partitionBundlePin (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    Fintype.card (H.PartitionBundlePin π b) =
      H.unorderedBundleMultiplicity π b.1 := by
  rw [Fintype.card_subtype]
  simp [PartitionBundlePin, unorderedBundleMultiplicity]

theorem partitionEdge_out_mk {t : ℕ} (b : PartitionEdge t) :
    s(b.1.out.1, b.1.out.2) = b.1 :=
  Quot.out_eq b.1

theorem partitionEdge_out_ne {t : ℕ} (b : PartitionEdge t) :
    b.1.out.1 ≠ b.1.out.2 := by
  intro h
  have hdiag : b.1.IsDiag := by
    rw [← partitionEdge_out_mk b, Sym2.mk_isDiag_iff]
    exact h
  exact (SimpleGraph.not_isDiag_of_mem_edgeFinset b.2) hdiag

/-- The point coordinates in one occurrence-level bundle. -/
def partitionBundlePoint (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → Vec3 ℝ :=
  fun e ↦ p e.1

/-- Sign comparing the stored orientation of a pin occurrence with the
orientation selected by `Sym2.out` for its unordered block bundle. -/
noncomputable def partitionBundleSign (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → ℝ :=
  fun e ↦ if π (H.left e.1) = b.1.out.1 then 1 else -1

theorem partitionBundleSign_ne_zero (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.partitionBundleSign π b e ≠ 0 := by
  classical
  by_cases h : π (H.left e.1) = b.1.out.1 <;>
    simp [partitionBundleSign, h]

/-- All pin constraints in one unordered block bundle, before grounding. -/
noncomputable def blockBundleOperator (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    (Fin t → Twist ℝ) →ₗ[ℝ] (H.PartitionBundlePin π b → Vec3 ℝ) :=
  LinearMap.pi fun e ↦
    (Twist.evalLinear (p e.1)).comp
      (assignmentDifferenceLinear (π (H.left e.1)) (π (H.right e.1)))

@[simp] theorem blockBundleOperator_apply (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t)
    (X : Fin t → Twist ℝ) (e : H.PartitionBundlePin π b) :
    H.blockBundleOperator π p b X e =
      Twist.eval
        (X (π (H.left e.1)) - X (π (H.right e.1))) (p e.1) := by
  simp [blockBundleOperator, assignmentDifferenceLinear]

/-- The oriented relative twist of every occurrence is the selected bundle
relative twist, multiplied by its explicit sign. -/
theorem occurrenceDifference_eq_sign_smul (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (X : Fin t → Twist ℝ) (e : H.PartitionBundlePin π b) :
    X (π (H.left e.1)) - X (π (H.right e.1)) =
      H.partitionBundleSign π b e • (X b.1.out.1 - X b.1.out.2) := by
  classical
  have he : s(π (H.left e.1), π (H.right e.1)) = b.1 :=
    (Finset.mem_filter.mp e.2).2
  have he' : s(π (H.left e.1), π (H.right e.1)) =
      s(b.1.out.1, b.1.out.2) :=
    he.trans (partitionEdge_out_mk b).symm
  rcases Sym2.eq_iff.mp he' with h | h
  · rcases h with ⟨hl, hr⟩
    simp [partitionBundleSign, hl, hr]
  · rcases h with ⟨hl, hr⟩
    have hne : b.1.out.2 ≠ b.1.out.1 := (partitionEdge_out_ne b).symm
    simp [partitionBundleSign, hl, hr, hne]

/-- Explicit factorization of a bundle through one relative twist and its
signed occurrence evaluations. -/
theorem blockBundleOperator_eq_signed_comp (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    H.blockBundleOperator π p b =
      (Twist.signedBundleLinear (H.partitionBundlePoint π p b)
        (H.partitionBundleSign π b)).comp
        (assignmentDifferenceLinear b.1.out.1 b.1.out.2) := by
  apply LinearMap.ext
  intro X
  funext e
  rw [H.blockBundleOperator_apply]
  simp only [LinearMap.comp_apply, Twist.signedBundleLinear_apply,
    assignmentDifferenceLinear]
  rw [H.occurrenceDifference_eq_sign_smul π b X e]
  exact (Twist.evalLinear (p e.1)).map_smul
    (H.partitionBundleSign π b e) (X b.1.out.1 - X b.1.out.2)

/-- Each unordered bundle pays at most its already-proved `0,3,5,6`
capacity, with no genericity or rank premise. -/
theorem finrank_range_blockBundleOperator_le_capacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (b : PartitionEdge t) :
    Module.finrank ℝ (LinearMap.range (H.blockBundleOperator π p b)) ≤
      pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
  rw [H.blockBundleOperator_eq_signed_comp]
  calc
    Module.finrank ℝ
        (LinearMap.range
          ((Twist.signedBundleLinear (H.partitionBundlePoint π p b)
            (H.partitionBundleSign π b)).comp
            (assignmentDifferenceLinear b.1.out.1 b.1.out.2))) ≤
        Module.finrank ℝ
          (LinearMap.range
            (Twist.signedBundleLinear (H.partitionBundlePoint π p b)
              (H.partitionBundleSign π b))) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    _ ≤ pinCapacity (Fintype.card (H.PartitionBundlePin π b)) :=
      Twist.finrank_range_signedBundleLinear_le_pinCapacity_card _ _
        (H.partitionBundleSign_ne_zero π b)
    _ = pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      rw [H.card_partitionBundlePin]

/-- Rigidity pulls back from bodies to any surjective quotient of the body
set: a block-constant motion is in particular a body motion. -/
theorem twistRigidAt_blocks_of_surjective (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (hπ : Function.Surjective π)
    (p : H.Pin → Vec3 ℝ) (hRigid : TwistRigidAt H.left H.right p) :
    TwistRigidAt (π ∘ H.left) (π ∘ H.right) p := by
  intro X hX
  have hBody : IsTwistMotion H.left H.right p (X ∘ π) := by
    intro e
    exact hX e
  obtain ⟨Y, hY⟩ := hRigid (X ∘ π) hBody
  refine ⟨Y, ?_⟩
  funext i
  obtain ⟨body, hbody⟩ := hπ i
  have hi := congrFun hY body
  simpa [Function.comp_apply, hbody] using hi

/-- All crossing constraints of a grounded block assignment, grouped by
their unordered block bundle.  Internal pins are omitted because a
block-constant twist makes their relative twist identically zero. -/
noncomputable def groupedGroundedBlockOperator (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) (p : H.Pin → Vec3 ℝ) (root : Fin t) :
    (OffRoot root → Twist ℝ) →ₗ[ℝ]
      ((b : PartitionEdge t) → H.PartitionBundlePin π b → Vec3 ℝ) :=
  LinearMap.pi fun b ↦
    (H.blockBundleOperator π p b).comp (extendGroundedLinear root)

@[simp] theorem groupedGroundedBlockOperator_apply
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (root : Fin t)
    (X : OffRoot root → Twist ℝ) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.groupedGroundedBlockOperator π p root X b e =
      Twist.eval
        (extendGrounded root X (π (H.left e.1)) -
          extendGrounded root X (π (H.right e.1))) (p e.1) := by
  simp [groupedGroundedBlockOperator, H.blockBundleOperator_apply,
    extendGroundedLinear]

/-- Under pointwise twist rigidity, the grouped grounded block operator is
injective.  This is the lower-rank half of partition necessity. -/
theorem groupedGroundedBlockOperator_injective_of_twistRigidAt
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (p : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right p) (root : Fin t) :
    Function.Injective (H.groupedGroundedBlockOperator π p root) := by
  classical
  have hBlockRigid : TwistRigidAt (π ∘ H.left) (π ∘ H.right) p :=
    H.twistRigidAt_blocks_of_surjective π hπ p hRigid
  have hGroundInjective : Function.Injective
      (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p) :=
    (groundedPinOperator_injective_iff_twistRigidAt
      root (π ∘ H.left) (π ∘ H.right) p).2 hBlockRigid
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.2
  intro X hX
  have hGroundZero :
      groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p X = 0 := by
    funext e
    by_cases heq : π (H.left e) = π (H.right e)
    · simp [groundedPinOperator_apply, Function.comp_apply, heq,
        Twist.eval, Vec3.cross]
    · let b : PartitionEdge t :=
        ⟨s(π (H.left e), π (H.right e)), by
          simp [Sym2.mk_isDiag_iff, heq]⟩
      let eb : H.PartitionBundlePin π b := ⟨e, by
        simp [PartitionBundlePin, b]⟩
      have hGrouped := congrFun (congrFun hX b) eb
      simpa [groundedPinOperator_apply, Function.comp_apply,
        H.groupedGroundedBlockOperator_apply] using hGrouped
  exact hGroundInjective (by simpa using hGroundZero)

/-- The grouped grounded operator has at least the full dimension of the
grounded block-twist space. -/
theorem six_mul_pred_le_groupedGroundedBlockOperator_rank
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (p : H.Pin → Vec3 ℝ)
    (hRigid : TwistRigidAt H.left H.right p) (root : Fin t) :
    6 * (t - 1) ≤
      Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) := by
  have hinj := H.groupedGroundedBlockOperator_injective_of_twistRigidAt
    π hπ p hRigid root
  have hker : LinearMap.ker (H.groupedGroundedBlockOperator π p root) = ⊥ :=
    LinearMap.ker_eq_bot.2 hinj
  have hRN := (H.groupedGroundedBlockOperator π p root).finrank_range_add_finrank_ker
  rw [hker] at hRN
  simp only [finrank_bot, add_zero] at hRN
  have hcard : Fintype.card (OffRoot root) = t - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin t ↦ i = root)]
    simp
  have hdomain : Module.finrank ℝ (OffRoot root → Twist ℝ) =
      6 * (t - 1) := by
    rw [Module.finrank_pi_fintype]
    simp [hcard, Nat.mul_comm]
  rw [← hdomain, ← hRN]

/-- The grouped operator's rank is at most the sum of the proved capacities
of its unordered bundles. -/
theorem groupedGroundedBlockOperator_rank_le_partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 ℝ) (root : Fin t) :
    Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) ≤
      H.partitionCapacity π := by
  classical
  calc
    Module.finrank ℝ
        (LinearMap.range (H.groupedGroundedBlockOperator π p root)) ≤
        ∑ b : PartitionEdge t,
          Module.finrank ℝ
            (LinearMap.range
              ((H.blockBundleOperator π p b).comp
                (extendGroundedLinear root))) := by
      exact finrank_range_pi_le_sum fun b ↦
        (H.blockBundleOperator π p b).comp (extendGroundedLinear root)
    _ ≤ ∑ b : PartitionEdge t,
        pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        Module.finrank ℝ
            (LinearMap.range
              ((H.blockBundleOperator π p b).comp
                (extendGroundedLinear root))) ≤
            Module.finrank ℝ
              (LinearMap.range (H.blockBundleOperator π p b)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
        _ ≤ pinCapacity (H.unorderedBundleMultiplicity π b.1) :=
          H.finrank_range_blockBundleOperator_le_capacity π p b
    _ = H.partitionCapacity π := by
      unfold partitionCapacity
      symm
      apply Finset.sum_subtype
      intro b
      rfl

/-- Pointwise twist rigidity forces every body partition to satisfy the
body--pin `0,3,5,6` capacity inequality. -/
theorem partitionCondition_of_twistRigidAt (H : BodyPinIncidence)
    (p : H.Pin → Vec3 ℝ) (hRigid : TwistRigidAt H.left H.right p) :
    H.PartitionCondition := by
  intro t π hπ
  by_cases ht : t = 0
  · subst t
    simp
  · let root : Fin t := ⟨0, Nat.pos_of_ne_zero ht⟩
    exact (H.six_mul_pred_le_groupedGroundedBlockOperator_rank
      π hπ p hRigid root).trans
        (H.groupedGroundedBlockOperator_rank_le_partitionCapacity π p root)

/-- Existential rigid twist realizability implies the complete partition
condition. -/
theorem partitionCondition_of_hasRigidTwistRealization
    (H : BodyPinIncidence)
    (hRigid : HasRigidTwistRealization (k := ℝ) H.left H.right) :
    H.PartitionCondition := by
  obtain ⟨p, hp⟩ := hRigid
  exact H.partitionCondition_of_twistRigidAt p hp

end BodyPinIncidence

end RB31E2E


end
end BundleSource0059

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0059/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0059.json"

section BundleSource0060
/- Source: Papers/RigidityFieldCapacity.lean -/




@[expose] public section

/-!
# Partition capacity over arbitrary coefficient fields

The occurrence-level signed-bundle proof is adapted from Dongzhe Zheng's
Apache-2.0 `TwistNecessity.lean`, commit
`e457fde9100c9b7226bd4d81af6860f210a531ab`. The same actual operators are
used over an arbitrary field, so the rational function coefficient field
in the quantitative proof receives the literal `0,3,5,6` capacity bound.
-/

namespace RB31E2E.BodyPinIncidence

noncomputable section

variable {k : Type*} [Field k]

/-- The point coordinates in one occurrence-level bundle. -/
def partitionBundlePointK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → Vec3 k :=
  fun e ↦ p e.1

/-- Sign comparing the stored orientation of a pin occurrence with the
orientation selected by `Sym2.out` for its unordered block bundle. -/
noncomputable def partitionBundleSignK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t) :
    H.PartitionBundlePin π b → k :=
  fun e ↦ if π (H.left e.1) = b.1.out.1 then 1 else -1

theorem partitionBundleSign_ne_zeroK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.partitionBundleSignK (k := k) π b e ≠ 0 := by
  classical
  by_cases h : π (H.left e.1) = b.1.out.1 <;>
    simp [partitionBundleSignK, h]

/-- All pin constraints in one unordered block bundle, before grounding. -/
noncomputable def blockBundleOperatorK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    (Fin t → Twist k) →ₗ[k] (H.PartitionBundlePin π b → Vec3 k) :=
  LinearMap.pi fun e ↦
    (Twist.evalLinear (p e.1)).comp
      (assignmentDifferenceLinear (π (H.left e.1)) (π (H.right e.1)))

@[simp] theorem blockBundleOperator_applyK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t)
    (X : Fin t → Twist k) (e : H.PartitionBundlePin π b) :
    H.blockBundleOperatorK π p b X e =
      Twist.eval
        (X (π (H.left e.1)) - X (π (H.right e.1))) (p e.1) := by
  simp [blockBundleOperatorK, assignmentDifferenceLinear]

/-- The oriented relative twist of every occurrence is the selected bundle
relative twist, multiplied by its explicit sign. -/
theorem occurrenceDifference_eq_sign_smulK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (b : PartitionEdge t)
    (X : Fin t → Twist k) (e : H.PartitionBundlePin π b) :
    X (π (H.left e.1)) - X (π (H.right e.1)) =
      H.partitionBundleSignK (k := k) π b e • (X b.1.out.1 - X b.1.out.2) := by
  classical
  have he : s(π (H.left e.1), π (H.right e.1)) = b.1 :=
    (Finset.mem_filter.mp e.2).2
  have he' : s(π (H.left e.1), π (H.right e.1)) =
      s(b.1.out.1, b.1.out.2) :=
    he.trans (partitionEdge_out_mk b).symm
  rcases Sym2.eq_iff.mp he' with h | h
  · rcases h with ⟨hl, hr⟩
    simp [partitionBundleSignK, hl, hr]
  · rcases h with ⟨hl, hr⟩
    have hne : b.1.out.2 ≠ b.1.out.1 := (partitionEdge_out_ne b).symm
    simp [partitionBundleSignK, hl, hr, hne]

/-- Explicit factorization of a bundle through one relative twist and its
signed occurrence evaluations. -/
theorem blockBundleOperator_eq_signed_compK (H : BodyPinIncidence) {t : ℕ}
    (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    H.blockBundleOperatorK π p b =
      (Twist.signedBundleLinear (H.partitionBundlePointK π p b)
        (H.partitionBundleSignK (k := k) π b)).comp
        (assignmentDifferenceLinear b.1.out.1 b.1.out.2) := by
  apply LinearMap.ext
  intro X
  funext e
  rw [H.blockBundleOperator_applyK]
  simp only [LinearMap.comp_apply, Twist.signedBundleLinear_apply,
    assignmentDifferenceLinear]
  rw [H.occurrenceDifference_eq_sign_smulK π b X e]
  exact (Twist.evalLinear (p e.1)).map_smul
    (H.partitionBundleSignK (k := k) π b e) (X b.1.out.1 - X b.1.out.2)

/-- Each unordered bundle pays at most its already-proved `0,3,5,6`
capacity, with no genericity or rank premise. -/
theorem finrank_range_blockBundleOperator_le_capacityK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (b : PartitionEdge t) :
    Module.finrank k (LinearMap.range (H.blockBundleOperatorK π p b)) ≤
      pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
  rw [H.blockBundleOperator_eq_signed_compK]
  calc
    Module.finrank k
        (LinearMap.range
          ((Twist.signedBundleLinear (H.partitionBundlePointK π p b)
            (H.partitionBundleSignK (k := k) π b)).comp
            (assignmentDifferenceLinear b.1.out.1 b.1.out.2))) ≤
        Module.finrank k
          (LinearMap.range
            (Twist.signedBundleLinear (H.partitionBundlePointK π p b)
              (H.partitionBundleSignK (k := k) π b))) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    _ ≤ pinCapacity (Fintype.card (H.PartitionBundlePin π b)) :=
      Twist.finrank_range_signedBundleLinear_le_pinCapacity_card _ _
        (H.partitionBundleSign_ne_zeroK π b)
    _ = pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      rw [H.card_partitionBundlePin]

/-- All crossing constraints of a grounded block assignment, grouped by
their unordered block bundle.  Internal pins are omitted because a
block-constant twist makes their relative twist identically zero. -/
noncomputable def groupedGroundedBlockOperatorK (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) (p : H.Pin → Vec3 k) (root : Fin t) :
    (OffRoot root → Twist k) →ₗ[k]
      ((b : PartitionEdge t) → H.PartitionBundlePin π b → Vec3 k) :=
  LinearMap.pi fun b ↦
    (H.blockBundleOperatorK π p b).comp (extendGroundedLinear root)

@[simp] theorem groupedGroundedBlockOperator_applyK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t)
    (X : OffRoot root → Twist k) (b : PartitionEdge t)
    (e : H.PartitionBundlePin π b) :
    H.groupedGroundedBlockOperatorK π p root X b e =
      Twist.eval
        (extendGrounded root X (π (H.left e.1)) -
          extendGrounded root X (π (H.right e.1))) (p e.1) := by
  simp [groupedGroundedBlockOperatorK, H.blockBundleOperator_applyK,
    extendGroundedLinear]

/-- The grouped operator's rank is at most the sum of the proved capacities
of its unordered bundles. -/
theorem groupedGroundedBlockOperator_rank_le_partitionCapacityK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    Module.finrank k
        (LinearMap.range (H.groupedGroundedBlockOperatorK π p root)) ≤
      H.partitionCapacity π := by
  classical
  calc
    Module.finrank k
        (LinearMap.range (H.groupedGroundedBlockOperatorK π p root)) ≤
        ∑ b : PartitionEdge t,
          Module.finrank k
            (LinearMap.range
              ((H.blockBundleOperatorK π p b).comp
                (extendGroundedLinear root))) := by
      exact finrank_range_pi_le_sum fun b ↦
        (H.blockBundleOperatorK π p b).comp (extendGroundedLinear root)
    _ ≤ ∑ b : PartitionEdge t,
        pinCapacity (H.unorderedBundleMultiplicity π b.1) := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        Module.finrank k
            (LinearMap.range
              ((H.blockBundleOperatorK π p b).comp
                (extendGroundedLinear root))) ≤
            Module.finrank k
              (LinearMap.range (H.blockBundleOperatorK π p b)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
        _ ≤ pinCapacity (H.unorderedBundleMultiplicity π b.1) :=
          H.finrank_range_blockBundleOperator_le_capacityK π p b
    _ = H.partitionCapacity π := by
      unfold partitionCapacity
      symm
      apply Finset.sum_subtype
      intro b
      rfl


/-- Grouping occurrences by unordered block pairs changes only the output
indexing and deletes identically zero internal rows. It preserves the
actual kernel. -/
theorem ker_groupedGroundedBlockOperatorK
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    (H.groupedGroundedBlockOperatorK π p root).ker =
      (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).ker := by
  classical
  ext X
  simp only [LinearMap.mem_ker]
  constructor
  · intro hX
    funext e
    by_cases heq : π (H.left e) = π (H.right e)
    · simp [groundedPinOperator_apply, heq, Twist.eval, Vec3.cross]
    · let b : PartitionEdge t := ⟨s(π (H.left e), π (H.right e)), by
        simp [Sym2.mk_isDiag_iff, heq]⟩
      let eb : H.PartitionBundlePin π b := ⟨e, by simp [PartitionBundlePin, b]⟩
      exact congrFun (congrFun hX b) eb
  · intro hX
    funext b e
    exact congrFun hX e.1

/-- The original grounded block operator has rank at most its actual
partition capacity, including all multiplicities and orientations. -/
theorem groundedBlockOperator_rank_le_partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    Module.finrank k (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).range ≤
      H.partitionCapacity π := by
  have h₁ := (H.groupedGroundedBlockOperatorK π p root).finrank_range_add_finrank_ker
  have h₂ := (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).finrank_range_add_finrank_ker
  rw [H.ker_groupedGroundedBlockOperatorK] at h₁
  have hrank := H.groupedGroundedBlockOperator_rank_le_partitionCapacityK π p root
  omega

/-- The partition count is realized as a lower bound on the literal
block-constant grounded kernel, over every field and at every placement. -/
theorem partitionDefect_le_groundedBlockKernel_finrank
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (p : H.Pin → Vec3 k) (root : Fin t) :
    6 * (t - 1) - H.partitionCapacity π ≤
      Module.finrank k (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).ker := by
  have hcap := H.groundedBlockOperator_rank_le_partitionCapacity π p root
  have hRN := (groundedPinOperator root (π ∘ H.left) (π ∘ H.right) p).finrank_range_add_finrank_ker
  have hcard : Fintype.card (OffRoot root) = t - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin t => i = root)]
    simp
  have hdim : Module.finrank k (OffRoot root → Twist k) = 6 * (t - 1) := by
    simp [Module.finrank_pi_fintype, hcard, Twist.finrank_twist, Nat.mul_comm]
  rw [hdim] at hRN
  omega

end

end RB31E2E.BodyPinIncidence

end
end BundleSource0060

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0060/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0060.json"

section BundleSource0061
/- Source: Papers/RigidityDefectMaximum.lean -/





@[expose] public section

/-!
# The complete generic pair-pin defect equality

The numerical maximum is taken over every surjective finite labelling of
the body set. Its upper bound is only the elementary six-per-body bound.
The theorem identifies this actual partition maximum with the kernel of
the literal grounded pin operator over independent coordinate parameters.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open RB31E2E
open RB31E2E.UniversalHomogeneousChart
open MotionQuotient

/-- At every placement and over every field, block-constant motions supply
the asserted partition lower bound for the actual grounded kernel. -/
theorem partitionCapacity_add_groundedKernel_finrank_ge
    {k : Type*} [Field k] (H : BodyPinIncidence) (root : H.Body)
    (p : H.Pin → RB31E2E.Vec3 k) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) :
    6 * (t - 1) ≤ H.partitionCapacity π +
      Module.finrank k (groundedPinOperator root H.left H.right p).ker := by
  let block := groundedPinOperator (π root) (π ∘ H.left) (π ∘ H.right) p
  have hrank := H.groundedBlockOperator_rank_le_partitionCapacity π p (π root)
  have hkernel := groundedKernel_finrank_le_of_surjective π hπ root H.left H.right p
  have hRN := block.finrank_range_add_finrank_ker
  have hcard : Fintype.card (OffRoot (π root)) = t - 1 := by
    rw [Fintype.card_subtype_compl (fun v : Fin t => v = π root)]
    simp
  have hdim : Module.finrank k (OffRoot (π root) → RB31E2E.Twist k) = 6 * (t - 1) := by
    simp [Module.finrank_pi_fintype, hcard, RB31E2E.Twist.finrank_twist, Nat.mul_comm]
  rw [hdim] at hRN
  change Module.finrank k block.range ≤ H.partitionCapacity π at hrank
  change Module.finrank k block.ker ≤
    Module.finrank k (groundedPinOperator root H.left H.right p).ker at hkernel
  omega

theorem partitionDefectMaximum_le_groundedKernel_finrank
    {k : Type*} [Field k] (H : BodyPinIncidence) (root : H.Body) (p : H.Pin → RB31E2E.Vec3 k) :
    partitionDefectMaximum H ≤
      Module.finrank k (groundedPinOperator root H.left H.right p).ker := by
  obtain ⟨t, π, hπ, hmax⟩ := partitionDefectMaximum_attained H root
  have h := partitionCapacity_add_groundedKernel_finrank_ge H root p π hπ
  omega

/-- Theorem 5.1, dimension formula over the full independent pin
coefficient field. No pair-pin rank, height, separation, or combinatorial
sparsity assertion is an input. -/
theorem genericGroundedKernel_finrank_eq_partitionDefectMaximum
    (H : BodyPinIncidence) (root : H.Body) :
    Module.finrank (GenericPinCoefficientField H.Pin)
      (groundedPinOperator root H.left H.right genericPins).ker =
      partitionDefectMaximum H := by
  exact le_antisymm
    (genericGroundedKernel_finrank_le_partitionDefectBound H root _
      (partitionDefectMaximum_is_bound H))
    (partitionDefectMaximum_le_groundedKernel_finrank H root genericPins)

end

end Papers.Rigidity.GenericPinIdeal

end
end BundleSource0061

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0061/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0061.json"

section BundleSource0062
/- Source: Papers/RigidityTwistSpace.lean -/



@[expose] public section

/-!
# The actual Euclidean twist space and evaluation maps

These definitions are independent of any rigidity theorem or partition formula.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

/-- Angular velocity and translational velocity. -/
abbrev Twist := Vec3 × Vec3

/-- The velocity of the point `p` under a Euclidean infinitesimal motion. -/
def evaluateTwist (p : Vec3) : Twist →ₗ[ℝ] Vec3 :=
  LinearMap.snd ℝ Vec3 Vec3 +
    ((crossProduct (R := ℝ)).flip p).comp (LinearMap.fst ℝ Vec3 Vec3)

@[simp] theorem evaluateTwist_apply (p : Vec3) (X : Twist) :
    evaluateTwist p X = X.2 + X.1 ⨯₃ p := rfl

/-- Evaluation on a genuine linear subspace of twists. -/
def restrictEvaluation (W : Submodule ℝ Twist) (p : Vec3) : W →ₗ[ℝ] Vec3 :=
  (evaluateTwist p).comp W.subtype

/-- Evaluation has rank at most two at every new pin.  A polynomial generic
rank bound implies this condition; that generic-to-universal bridge is a
separate obligation. -/
def SingularPinSpace (W : Submodule ℝ Twist) : Prop :=
  ∀ p : Vec3, Module.finrank ℝ (restrictEvaluation W p).range ≤ 2

/-- A finite virtual center is exactly the space of rotations fixing it. -/
def finiteCenterSpace (a : Vec3) : Submodule ℝ Twist :=
  (evaluateTwist a).ker

/-- An infinite projective center is represented by a nonzero direction `d`.
Its twists have angular velocity parallel to `d` and translation normal to it. -/
def infiniteCenterSpace (d : Vec3) : Submodule ℝ Twist where
  carrier := {X | X.1 ⨯₃ d = 0 ∧ X.2 ⬝ᵥ d = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    constructor
    · change (X.1 + Y.1) ⨯₃ d = 0
      rw [map_add, LinearMap.add_apply, hX.1, hY.1, add_zero]
    · change (X.2 + Y.2) ⬝ᵥ d = 0
      rw [add_dotProduct, hX.2, hY.2, add_zero]
  smul_mem' := by
    intro c X hX
    constructor
    · change (c • X.1) ⨯₃ d = 0
      rw [map_smul, LinearMap.smul_apply, hX.1, smul_zero]
    · change (c • X.2) ⬝ᵥ d = 0
      simp [smul_dotProduct, hX.2]

theorem evaluateTwist_surjective (p : Vec3) : Function.Surjective (evaluateTwist p) := by
  intro v
  exact ⟨(0, v), by simp⟩

theorem finrank_twist : Module.finrank ℝ Twist = 6 := by
  simp [Twist, Vec3]

theorem finrank_finiteCenterSpace (a : Vec3) :
    Module.finrank ℝ (finiteCenterSpace a) = 3 := by
  have h := (evaluateTwist a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (evaluateTwist_surjective a)] at h
  have hdim : 3 + Module.finrank ℝ (evaluateTwist a).ker = 6 := by
    simpa [finrank_twist, Vec3] using h
  change Module.finrank ℝ (evaluateTwist a).ker = 3
  omega


end Papers.Rigidity

end
end BundleSource0062

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0062/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0062.json"

section BundleSource0063
/- Source: Papers/RigidityPairPins.lean -/





@[expose] public section

/-!
# Exact pair-pin defect target (Theorem 5.1)

Bodies carry ordinary Euclidean twists; each pin imposes equality of the
velocities assigned by its two bodies. Rank is the attained maximum of the
actual real linear operator, and is not defined by a partition formula.
-/

namespace Papers.Rigidity

open scoped BigOperators
open scoped Classical

structure PairPinGraph (B E : Type) where
  left : E → B
  right : E → B
  loopless : ∀ e, left e ≠ right e

namespace PairPinGraph

variable {B E : Type}

/-- The occurrence-level compatibility operator, with three rows per pin. -/
def compatibilityOperator (J : PairPinGraph B E) (p : E → Vec3) :
    (B → Twist) →ₗ[ℝ] (E → Vec3) :=
  LinearMap.pi fun e =>
    (evaluateTwist (p e)).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.left e) -
        LinearMap.proj (R := ℝ) (φ := fun _ : B => Twist) (J.right e))

@[simp] theorem compatibilityOperator_apply
    (J : PairPinGraph B E) (p : E → Vec3) (X : B → Twist) (e : E) :
    compatibilityOperator J p X e =
      evaluateTwist (p e) (X (J.left e)) - evaluateTwist (p e) (X (J.right e)) := by
  simp [compatibilityOperator, sub_add_sub_comm]

noncomputable def pinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) : ℕ :=
  Module.finrank ℝ (compatibilityOperator J p).range

theorem pinRank_le [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) : pinRank J p ≤ 6 * Fintype.card B := by
  have h := LinearMap.finrank_range_le (compatibilityOperator J p)
  simpa [pinRank, Module.finrank_pi_fintype, finrank_twist, Nat.mul_comm] using h

noncomputable def genericPinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℕ := by
  classical
  exact Nat.findGreatest (fun r => ∃ p : E → Vec3, pinRank J p = r)
    (6 * Fintype.card B)

theorem pinRank_le_generic [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) : pinRank J p ≤ genericPinRank J := by
  classical
  exact Nat.le_findGreatest (pinRank_le J p) ⟨p, rfl⟩

theorem genericPinRank_attained [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ∃ p : E → Vec3, pinRank J p = genericPinRank J := by
  classical
  have h := Nat.findGreatest_spec
    (P := fun r => ∃ p : E → Vec3, pinRank J p = r)
    (pinRank_le J (0 : E → Vec3)) ⟨0, rfl⟩
  simpa [genericPinRank] using h

/-- Dimension of compatible motions modulo the six common rigid motions. -/
noncomputable def genericRelativeDof [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℕ :=
  6 * Fintype.card B - genericPinRank J - 6

def commonTwistMap : Twist →ₗ[ℝ] (B → Twist) :=
  LinearMap.pi fun _ => LinearMap.id

@[simp] theorem commonTwistMap_apply (X : Twist) (b : B) :
    commonTwistMap X b = X := rfl

theorem commonTwist_mem_ker (J : PairPinGraph B E) (p : E → Vec3) (X : Twist) :
    commonTwistMap X ∈ (compatibilityOperator J p).ker := by
  rw [LinearMap.mem_ker]
  ext e i
  simp

def commonTwistInKernel (J : PairPinGraph B E) (p : E → Vec3) :
    Twist →ₗ[ℝ] (compatibilityOperator J p).ker :=
  commonTwistMap.codRestrict _ (commonTwist_mem_ker J p)

theorem commonTwistInKernel_injective [Nonempty B]
    (J : PairPinGraph B E) (p : E → Vec3) : Function.Injective (commonTwistInKernel J p) := by
  intro X Y hXY
  obtain ⟨b⟩ := ‹Nonempty B›
  exact congrFun (congrArg Subtype.val hXY) b

/-- Actual compatible motions modulo the actual subspace of common motions. -/
abbrev RelativeMotionSpace (J : PairPinGraph B E) (p : E → Vec3) :=
  (compatibilityOperator J p).ker ⧸ (commonTwistInKernel J p).range

theorem relativeMotionSpace_rank_nullity [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (p : E → Vec3) :
    Module.finrank ℝ (RelativeMotionSpace J p) + pinRank J p + 6 =
      6 * Fintype.card B := by
  have hcommon : Module.finrank ℝ (commonTwistInKernel J p).range = 6 :=
    (LinearMap.finrank_range_of_inj (commonTwistInKernel_injective J p)).trans finrank_twist
  have hquot := (commonTwistInKernel J p).range.finrank_quotient_add_finrank
  have hrank := (compatibilityOperator J p).finrank_range_add_finrank_ker
  have htotal : Module.finrank ℝ (B → Twist) = 6 * Fintype.card B := by
    simp [Module.finrank_pi_fintype, finrank_twist, Nat.mul_comm]
  rw [hcommon] at hquot
  rw [htotal] at hrank
  change Module.finrank ℝ (RelativeMotionSpace J p) + 6 =
    Module.finrank ℝ (compatibilityOperator J p).ker at hquot
  unfold pinRank
  omega

theorem genericPinRank_add_six_le [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) : genericPinRank J + 6 ≤ 6 * Fintype.card B := by
  obtain ⟨p, hp⟩ := genericPinRank_attained J
  have h := relativeMotionSpace_rank_nullity J p
  rw [hp] at h
  omega

/-- At a maximum-rank placement the numerical definition is exactly the
dimension of the quotient by common Euclidean motions; no truncation alters it. -/
theorem genericRelativeDof_eq_finrank_quotient [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (p : E → Vec3) (hp : pinRank J p = genericPinRank J) :
    genericRelativeDof J = Module.finrank ℝ (RelativeMotionSpace J p) := by
  have h := relativeMotionSpace_rank_nullity J p
  rw [hp] at h
  unfold genericRelativeDof
  omega

def pinCapacity : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 6

noncomputable def multiplicity [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) (i j : Fin t) : ℕ := by
  classical
  exact (Finset.univ.filter fun e =>
    (π (J.left e) = i ∧ π (J.right e) = j) ∨
    (π (J.left e) = j ∧ π (J.right e) = i)).card

noncomputable def partitionCapacity [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) : ℕ :=
  ∑ i : Fin t, ∑ j ∈ Finset.univ.filter (i < ·), pinCapacity (multiplicity J π i j)

/-- Empty labels do not count as blocks. Every partition of a nonempty
finite body set has such a labelling with at most `card B` labels. -/
noncomputable def labelledPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) : ℤ :=
  6 * (((Finset.univ.image π).card : ℤ) - 1) - (partitionCapacity J π : ℤ)

/-- The labels used in the maximization represent every equivalence-relation
partition of the finite body set, without a restriction on its number of blocks. -/
theorem exists_partition_labelling [Fintype B] (s : Setoid B) :
    ∃ π : B → Fin (Fintype.card B), ∀ i j, π i = π j ↔ s.r i j := by
  classical
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  have hc : Fintype.card (Quotient s) ≤ Fintype.card B :=
    Fintype.card_le_of_surjective (Quotient.mk s) Quotient.mk_surjective
  let e : Quotient s ↪ Fin (Fintype.card B) :=
    (Fintype.equivFin (Quotient s)).toEmbedding.trans
      ⟨Fin.castLE hc, Fin.castLE_injective hc⟩
  refine ⟨fun b => e (Quotient.mk s b), ?_⟩
  intro i j
  rw [e.injective.eq_iff, Quotient.eq]

noncomputable def maxPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℤ :=
  (Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π)).max'
    (Finset.image_nonempty.mpr ⟨Fintype.equivFin B, Finset.mem_univ _⟩)

theorem multiplicity_const_of_ne [Fintype E] (J : PairPinGraph B E)
    {t : ℕ} (a i j : Fin t) (hij : i ≠ j) :
    multiplicity J (fun _ => a) i j = 0 := by
  classical
  have hn : ¬ ((a = i ∧ a = j) ∨ (a = j ∧ a = i)) := by
    rintro (⟨hi, hj⟩ | ⟨hj, hi⟩)
    · exact hij (hi.symm.trans hj)
    · exact hij (hi.symm.trans hj)
  simp [multiplicity, hn]

theorem partitionCapacity_const [Fintype E] (J : PairPinGraph B E)
    {t : ℕ} (a : Fin t) : partitionCapacity J (fun _ => a) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  rw [multiplicity_const_of_ne J a i j hij]
  rfl

theorem labelledPartitionDefect_const [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) {t : ℕ} (a : Fin t) :
    labelledPartitionDefect J (fun _ => a) = 0 := by
  classical
  simp [labelledPartitionDefect, partitionCapacity_const,
    Finset.image_const Finset.univ_nonempty]

/-- The one-block partition gives zero defect, so the integer maximum is
nonnegative before any rigidity or incidence theorem is applied. -/
theorem maxPartitionDefect_nonneg [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) : 0 ≤ maxPartitionDefect J := by
  classical
  let a : Fin (Fintype.card B) := ⟨0, Fintype.card_pos⟩
  have hm : labelledPartitionDefect J (fun _ => a) ∈
      Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π) :=
    Finset.mem_image.mpr ⟨fun _ => a, Finset.mem_univ _, rfl⟩
  have h := Finset.le_max' _ _ hm
  simpa [maxPartitionDefect, labelledPartitionDefect_const] using h

/-- The finite maximum is attained by an actual partition labelling. -/
theorem maxPartitionDefect_attained [Fintype B] [Fintype E]
    (J : PairPinGraph B E) :
    ∃ π : B → Fin (Fintype.card B), labelledPartitionDefect J π = maxPartitionDefect J := by
  classical
  have hm := Finset.max'_mem
    (Finset.univ.image (fun π : B → Fin (Fintype.card B) => labelledPartitionDefect J π))
    (Finset.image_nonempty.mpr ⟨Fintype.equivFin B, Finset.mem_univ _⟩)
  obtain ⟨π, _, hπ⟩ := Finset.mem_image.mp hm
  exact ⟨π, hπ⟩

noncomputable def singletonPartitionDefect [Fintype B] [Fintype E]
    (J : PairPinGraph B E) : ℤ :=
  labelledPartitionDefect J (Fintype.equivFin B)

/-- Distinct body pairs are not rigidly linked at generic pin parameters. -/
def NoMergedBodies [Fintype B] [Fintype E] (J : PairPinGraph B E) : Prop :=
  ∀ i j : B, i ≠ j → ∃ p : E → Vec3,
    pinRank J p = genericPinRank J ∧
    ∃ X : B → Twist, X ∈ (compatibilityOperator J p).ker ∧ X i ≠ X j

/-- No parallel pin occurrences. -/
def IsSimple (J : PairPinGraph B E) : Prop :=
  Function.Injective (fun e => s(J.left e, J.right e))

end PairPinGraph

/-- The full three-part assertion of Theorem 5.1, recorded as an unproved
target proposition. A checked definition is not a proof of this claim. -/
def PairPinDefectClaim : Prop :=
  ∀ (B E : Type) [Fintype B] [Fintype E] [Nonempty B] (J : PairPinGraph B E),
    (J.genericRelativeDof : ℤ) = J.maxPartitionDefect ∧
    (J.NoMergedBodies →
      (J.genericRelativeDof : ℤ) = J.singletonPartitionDefect ∧
      (J.IsSimple → J.genericPinRank = 3 * Fintype.card E))

end Papers.Rigidity

end
end BundleSource0063

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0063/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0063.json"

section BundleSource0064
/- Source: Papers/RigidityPairPinIncidence.lean -/




@[expose] public section

namespace Papers.Rigidity.PairPinGraph
noncomputable section
variable {B E : Type} [Fintype B] [Fintype E]

/-- The imported incidence structure carries exactly the same endpoints,
occurrences and looplessness as the paper-facing pair-pin graph. -/
abbrev toBodyPinIncidence (J : PairPinGraph B E) : RB31E2E.BodyPinIncidence where
  Body := B
  Pin := E
  bodyFinite := inferInstance
  pinFinite := inferInstance
  bodyDecidableEq := Classical.decEq B
  pinDecidableEq := Classical.decEq E
  left := J.left
  right := J.right
  loopless := J.loopless

end
end Papers.Rigidity.PairPinGraph

end
end BundleSource0064

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0064/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0064.json"

section BundleSource0065
/- Source: Papers/RigidityPairPinGenericity.lean -/





@[expose] public section

/-!
# Faithfulness of generic pin rank over the real numbers

Grounding removes exactly the common Euclidean motions and does not alter
any output constraint. The rational-function matrix rank is then proved
equal to the attained maximum rank of the original real pin operator.
-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

open RB31E2E.GroundedTwistPolynomial
open GenericPinIdeal

variable {B E : Type} [Fintype B] [Fintype E]

theorem zheng_motionOperator_eq (J : PairPinGraph B E) (p : E → Vec3) :
    MotionQuotient.motionOperator J.left J.right p = compatibilityOperator J p := by
  apply LinearMap.ext
  intro X
  funext e i
  fin_cases i <;>
    simp [MotionQuotient.motionOperator_apply, compatibilityOperator_apply,
      RB31E2E.Twist.eval, RB31E2E.Vec3.cross, cross_apply]

/-- Every ungrounded output is also obtained after subtracting the twist
of the grounding body. The actual constraint ranges are equal. -/
theorem range_groundedPinOperator_eq [DecidableEq B]
    (J : PairPinGraph B E) (root : B) (p : E → Vec3) :
    (RB31E2E.groundedPinOperator root J.left J.right p).range =
      (compatibilityOperator J p).range := by
  rw [← zheng_motionOperator_eq]
  apply le_antisymm
  · rintro y ⟨X, rfl⟩
    refine ⟨RB31E2E.extendGrounded root X, ?_⟩
    funext e
    simp [MotionQuotient.motionOperator_apply, RB31E2E.groundedPinOperator_apply,
      RB31E2E.Twist.eval_sub]
  · rintro y ⟨X, rfl⟩
    let Y : RB31E2E.OffRoot root → RB31E2E.Twist ℝ := fun w => X w.1 - X root
    have hext : RB31E2E.extendGrounded root Y = fun v => X v - X root := by
      funext v
      by_cases hv : v = root
      · subst v
        simp
      · simp [RB31E2E.extendGrounded, Y, hv]
    refine ⟨Y, ?_⟩
    funext e
    rw [RB31E2E.groundedPinOperator_apply, hext]
    have hdiff : (X (J.left e) - X root) - (X (J.right e) - X root) =
        X (J.left e) - X (J.right e) := by abel
    rw [hdiff, RB31E2E.Twist.eval_sub, MotionQuotient.motionOperator_apply]

theorem pinRank_eq_groundedMatrix_rank [DecidableEq B]
    (J : PairPinGraph B E) (root : B) (p : E → Vec3) :
    pinRank J p = (groundedPinMatrix root J.left J.right p).rank := by
  rw [groundedPinMatrix_rank_eq_operator_rank, range_groundedPinOperator_eq]
  rfl

/-- The independent-parameter rank equals the maximum real rank of the
actual pin operator. Every occurrence and all three coordinate rows are
preserved. -/
theorem genericPinRank_eq_genericMotionMatrix_rank [DecidableEq B]
    (J : PairPinGraph B E) (root : B) :
    genericPinRank J = (genericMotionMatrix root J.left J.right).rank := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := genericPinRank_attained J
    rw [← hp, pinRank_eq_groundedMatrix_rank J root p]
    exact real_groundedPinMatrix_rank_le_generic root J.left J.right p
  · obtain ⟨p, hp⟩ := exists_real_groundedPinMatrix_rank_eq_generic root J.left J.right
    rw [← hp, ← pinRank_eq_groundedMatrix_rank J root p]
    exact pinRank_le_generic J p

/-- Generic dimension modulo the common Euclidean motions is the actual
kernel dimension over the independent rational pin coordinates. -/
theorem genericRelativeDof_eq_genericGroundedKernel_finrank [DecidableEq B]
    (J : PairPinGraph B E) (root : B) :
    genericRelativeDof J =
      Module.finrank (PinField E)
        (RB31E2E.groundedPinOperator root J.left J.right genericPins).ker := by
  have hRN := genericMotion_rank_add_nullity root J.left J.right
  have hcard : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨root⟩
  rw [← genericPinRank_eq_genericMotionMatrix_rank J root] at hRN
  unfold genericRelativeDof
  omega


/-- At every real maximum-rank placement, grounding has exactly the
paper's generic relative number of degrees of freedom. -/
theorem realGroundedKernel_finrank_eq_genericRelativeDof [DecidableEq B]
    (J : PairPinGraph B E) (root : B) (p : E → Vec3)
    (hp : pinRank J p = genericPinRank J) :
    Module.finrank ℝ (RB31E2E.groundedPinOperator root J.left J.right p).ker =
      genericRelativeDof J := by
  have hRN := (RB31E2E.groundedPinOperator root J.left J.right p).finrank_range_add_finrank_ker
  rw [range_groundedPinOperator_eq] at hRN
  have hcard : Fintype.card (RB31E2E.OffRoot root) = Fintype.card B - 1 := by
    rw [Fintype.card_subtype_compl (fun b : B => b = root)]
    simp
  have hdim : Module.finrank ℝ (RB31E2E.OffRoot root → RB31E2E.Twist ℝ) =
      6 * (Fintype.card B - 1) := by
    simp [Module.finrank_pi_fintype, hcard, RB31E2E.Twist.finrank_twist, Nat.mul_comm]
  rw [hdim] at hRN
  change pinRank J p + _ = _ at hRN
  rw [hp] at hRN
  have hpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨root⟩
  unfold genericRelativeDof
  omega

end

end Papers.Rigidity.PairPinGraph

end
end BundleSource0065

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0065/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0065.json"

section BundleSource0066
/- Source: Papers/RigidityPartitionCorrespondence.lean -/







@[expose] public section

/-!
# Exact correspondence of the two partition maxima

Unused finite labels have zero incident capacity. Injective relabelling
preserves every nonempty unordered bundle, and normalizing the used labels
turns every paper-facing labelling into a surjection. This identifies the
integer maximum in Theorem 5.1 with the natural maximum used in the generic
kernel proof, including all partitions and the zero-defect case.
-/

noncomputable section

namespace RB31E2E.BodyPinIncidence

/-- Only unordered pairs represented by crossing occurrences can contribute. -/
def actualPairs (H : BodyPinIncidence) {I : Type} [DecidableEq I]
    (label : H.Body → I) : Finset (Sym2 I) :=
  (Finset.univ.image fun e => s(label (H.left e), label (H.right e))).filter
    (fun b => ¬ b.IsDiag)

theorem capacityOn_eq_sum_actualPairs (H : BodyPinIncidence)
    {I : Type} [Fintype I] [DecidableEq I] (label : H.Body → I) :
    H.capacityOn label = ∑ b ∈ H.actualPairs label, pinCapacity (H.bundleMultiplicityOn label b) := by
  classical
  have hsub : H.actualPairs label ⊆ (⊤ : SimpleGraph I).edgeFinset := by
    intro b hb
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] using
      (Finset.mem_filter.mp hb).2
  unfold capacityOn
  symm
  apply Finset.sum_subset hsub
  intro b hb hnot
  have hdiag : ¬ b.IsDiag := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] using hb
  have hzero : H.bundleMultiplicityOn label b = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨e, Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩, hdiag⟩
  simp [hzero]

theorem bundleMultiplicityOn_comp_injective (H : BodyPinIncidence)
    {I J : Type} [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (label : H.Body → I) (b : Sym2 I) :
    H.bundleMultiplicityOn (f ∘ label) (b.map f) = H.bundleMultiplicityOn label b := by
  unfold bundleMultiplicityOn
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro e _
  change Sym2.map f s(label (H.left e), label (H.right e)) = Sym2.map f b ↔ _
  exact (Sym2.map.injective hf).eq_iff

theorem actualPairs_comp_injective (H : BodyPinIncidence)
    {I J : Type} [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (label : H.Body → I) :
    H.actualPairs (f ∘ label) = (H.actualPairs label).image (Sym2.map f) := by
  unfold actualPairs
  simp only [Function.comp_apply]
  rw [show (Finset.univ.image fun e => s(f (label (H.left e)), f (label (H.right e)))) =
      (Finset.univ.image fun e => s(label (H.left e), label (H.right e))).image
        (Sym2.map f) by rw [Finset.image_image] <;> rfl]
  rw [Finset.filter_image]
  apply congrArg (fun s : Finset (Sym2 I) => s.image (Sym2.map f))
  apply Finset.filter_congr
  intro b _
  exact not_congr (Sym2.isDiag_map hf)

/-- Adding unused labels or permuting labels cannot alter any capacity. -/
theorem capacityOn_comp_injective (H : BodyPinIncidence)
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) (label : H.Body → I) :
    H.capacityOn (f ∘ label) = H.capacityOn label := by
  rw [capacityOn_eq_sum_actualPairs, capacityOn_eq_sum_actualPairs,
    actualPairs_comp_injective H f hf label]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [bundleMultiplicityOn_comp_injective H f hf label b]
  · intro a ha b hb hab
    exact Sym2.map.injective hf hab

end RB31E2E.BodyPinIncidence

namespace Papers.Rigidity.PairPinGraph

open GenericPinIdeal

variable {B E : Type} [Fintype B] [Fintype E]

/-- Summing over unordered pairs is the same as summing once over `i < j`.
The equality is about the literal occurrence multiplicities. -/
theorem partitionCapacity_eq_incidenceCapacity (J : PairPinGraph B E)
    {t : ℕ} (π : B → Fin t) :
    partitionCapacity J π = J.toBodyPinIncidence.partitionCapacity π := by
  classical
  let H := J.toBodyPinIncidence
  have htop : (⊤ : SimpleGraph (Fin t)).edgeFinset =
      (Finset.univ.sym2.filter fun b => ¬ b.IsDiag) := by
    ext b
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet, Finset.mem_filter, Finset.sym2_univ, Finset.mem_univ, true_and]
  have hfilter : (Finset.univ : Finset (Fin t)).offDiag.filter (fun a => a.1 < a.2) =
      (Finset.univ ×ˢ Finset.univ).filter (fun a : Fin t × Fin t => a.1 < a.2) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
      true_and, Finset.mem_product]
    exact and_iff_right_of_imp ne_of_lt
  have hmult (i j : Fin t) : H.unorderedBundleMultiplicity π s(i,j) = multiplicity J π i j := by
    exact (H.unorderedBundleMultiplicity_mk π i j).trans rfl
  change _ = ∑ b ∈ (⊤ : SimpleGraph (Fin t)).edgeFinset,
    RB31E2E.pinCapacity (H.unorderedBundleMultiplicity π b)
  rw [htop, Finset.sum_sym2_filter_not_isDiag, hfilter, Finset.sum_filter, Finset.sum_product]
  simp only [partitionCapacity, Finset.sum_filter, hmult] <;> rfl

theorem partitionCapacity_comp_injective (J : PairPinGraph B E)
    {t n : ℕ} (f : Fin t → Fin n) (hf : Function.Injective f) (π : B → Fin t) :
    partitionCapacity J (f ∘ π) = partitionCapacity J π := by
  rw [partitionCapacity_eq_incidenceCapacity, partitionCapacity_eq_incidenceCapacity]
  exact J.toBodyPinIncidence.capacityOn_comp_injective f hf π

/-- Every labelling can be normalized to exactly its used labels, without
changing the capacity sum. -/
theorem normalize_partition_labelling (J : PairPinGraph B E)
    {n : ℕ} (π : B → Fin n) :
    ∃ σ : B → Fin ((Finset.univ.image π).card), Function.Surjective σ ∧
      partitionCapacity J σ = partitionCapacity J π := by
  classical
  let S := Finset.univ.image π
  let τ : B → S := fun b => ⟨π b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  have hτ : Function.Surjective τ := by
    intro a
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp a.2
    exact ⟨b, Subtype.ext hb⟩
  let e : S ≃ Fin S.card := S.equivFin
  let σ : B → Fin S.card := e ∘ τ
  let f : Fin S.card → Fin n := fun i => (e.symm i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have heq : f ∘ σ = π := by
    funext b
    simp [f, σ, τ]
  refine ⟨σ, e.surjective.comp hτ, ?_⟩
  calc
    partitionCapacity J σ = partitionCapacity J (f ∘ σ) :=
      (partitionCapacity_comp_injective J f hf σ).symm
    _ = partitionCapacity J π := congrArg (fun q : B → Fin n => partitionCapacity J q) heq

theorem labelledPartitionDefect_le_natMaximum [Nonempty B]
    (J : PairPinGraph B E) {n : ℕ} (π : B → Fin n) :
    labelledPartitionDefect J π ≤ (partitionDefectMaximum J.toBodyPinIncidence : ℤ) := by
  classical
  obtain ⟨σ, hσ, hcap⟩ := normalize_partition_labelling J π
  have hb := partitionDefectMaximum_is_bound J.toBodyPinIncidence _ σ hσ
  rw [← partitionCapacity_eq_incidenceCapacity, hcap] at hb
  have hpos : 0 < (Finset.univ.image π).card := by
    exact Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  unfold labelledPartitionDefect
  omega

theorem natDefect_le_paperMaximum [Nonempty B]
    (J : PairPinGraph B E) {t : ℕ} (π : B → Fin t) (hπ : Function.Surjective π) :
    (6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity π : ℕ) ≤
      (maxPartitionDefect J).toNat := by
  classical
  have ht : t ≤ Fintype.card B := by simpa using Fintype.card_le_of_surjective π hπ
  let f : Fin t → Fin (Fintype.card B) := Fin.castLE ht
  have hf : Function.Injective f := Fin.castLE_injective ht
  have hused : (Finset.univ.image (f ∘ π)).card = t := by
    rw [show Finset.univ.image (f ∘ π) = (Finset.univ : Finset (Fin t)).image f by
      rw [← Finset.image_image, Finset.image_univ_of_surjective hπ]]
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hle : labelledPartitionDefect J (f ∘ π) ≤ maxPartitionDefect J := by
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨f ∘ π, Finset.mem_univ _, rfl⟩)
  have hn := maxPartitionDefect_nonneg J
  have htpos : 0 < t := by
    obtain ⟨b⟩ := ‹Nonempty B›
    exact lt_of_le_of_lt (Nat.zero_le _) (π b).isLt
  rw [labelledPartitionDefect, hused, partitionCapacity_comp_injective J f hf π,
    partitionCapacity_eq_incidenceCapacity] at hle
  omega

/-- The natural maximum is exactly the integer maximum in the paper-facing
statement; truncation changes no result because the one-block defect is zero. -/
theorem maxPartitionDefect_eq_natMaximum [Nonempty B] (J : PairPinGraph B E) :
    maxPartitionDefect J = (partitionDefectMaximum J.toBodyPinIncidence : ℤ) := by
  classical
  apply le_antisymm
  · obtain ⟨π, hπ⟩ := maxPartitionDefect_attained J
    rw [← hπ]
    exact labelledPartitionDefect_le_natMaximum J π
  · obtain ⟨root⟩ := ‹Nonempty B›
    obtain ⟨t, π, hπ, hmax⟩ := partitionDefectMaximum_attained J.toBodyPinIncidence root
    have h := natDefect_le_paperMaximum J π hπ
    have hn := maxPartitionDefect_nonneg J
    rw [← hmax] at h
    omega

end Papers.Rigidity.PairPinGraph

end

end
end BundleSource0066

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0066/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0066.json"

section BundleSource0067
/- Source: Papers/RigidityPairPinDefect.lean -/





@[expose] public section

/-!
# The exact generic pair-pin dimension formula

The conclusion uses the original real compatibility operator and the
original integer maximum over all body partitions. The rational-function
proof and both directions of the statement correspondence are explicit
imports; no desired rank statement is stored in an input structure.
-/

namespace Papers.Rigidity

noncomputable section

/-- The dimension formula of Theorem 5.1 for every finite nonempty body set
and every finite loopless pin multigraph, with no restriction on the
numbers of bodies, pins, parallel occurrences or rigid clusters. -/
theorem pairPin_defect_dimension
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) :
    (J.genericRelativeDof : ℤ) = J.maxPartitionDefect := by
  classical
  obtain ⟨root⟩ := ‹Nonempty B›
  rw [PairPinGraph.maxPartitionDefect_eq_natMaximum]
  apply congrArg (fun n : ℕ => (n : ℤ))
  rw [PairPinGraph.genericRelativeDof_eq_genericGroundedKernel_finrank J root]
  exact GenericPinIdeal.genericGroundedKernel_finrank_eq_partitionDefectMaximum
    J.toBodyPinIncidence root

end

end Papers.Rigidity

end
end BundleSource0067

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0067/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0067.json"

section BundleSource0068
/- Source: Papers/RigidityPairPinRows.lean -/




@[expose] public section

/-!
# Actual pin rows and the rank statement in Theorem 5.1

This identifies the numerical full-row-rank conclusion with linear
independence of the literal three coordinate constraints at every pin.
-/

namespace Papers.Rigidity.PairPinGraph

variable {B E : Type}

def flattenPinCoordinates : (E → Vec3) ≃ₗ[ℝ] (E × Fin 3 → ℝ) where
  toFun y a := y a.1 a.2
  invFun y e i := y (e, i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- One literal coordinate row of a pin compatibility equation. -/
def pinRow (J : PairPinGraph B E) (p : E → Vec3) (a : E × Fin 3) :
    (B → Twist) →ₗ[ℝ] ℝ :=
  (LinearMap.proj a.2).comp ((LinearMap.proj a.1).comp (compatibilityOperator J p))

@[simp] theorem pinRow_apply (J : PairPinGraph B E) (p : E → Vec3)
    (a : E × Fin 3) (X : B → Twist) :
    pinRow J p a X =
      evaluateTwist (p a.1) (X (J.left a.1)) a.2 -
        evaluateTwist (p a.1) (X (J.right a.1)) a.2 := by
  simp [pinRow]

theorem linearIndependent_pinRows_iff_surjective [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) :
    LinearIndependent ℝ (pinRow J p) ↔ Function.Surjective (compatibilityOperator J p) := by
  classical
  let F := flattenPinCoordinates.toLinearMap.comp (compatibilityOperator J p)
  let b := (Pi.basisFun ℝ (E × Fin 3)).dualBasis
  have he : (fun a => F.dualMap (b a)) = pinRow J p := by
    funext a
    apply LinearMap.ext
    intro X
    simp [F, b, Module.Basis.dualBasis_apply, pinRow, flattenPinCoordinates]
  have hi : LinearIndependent ℝ (pinRow J p) ↔ Function.Injective F.dualMap := by
    rw [← he]
    constructor
    · exact LinearMap.injective_of_linearIndependent b.span_eq
    · intro h
      exact b.linearIndependent.map' F.dualMap (LinearMap.ker_eq_bot.mpr h)
  rw [hi, LinearMap.dualMap_injective_iff]
  constructor
  · intro h y
    obtain ⟨X, hX⟩ := h (flattenPinCoordinates y)
    exact ⟨X, flattenPinCoordinates.injective hX⟩
  · intro h y
    obtain ⟨X, hX⟩ := h (flattenPinCoordinates.symm y)
    exact ⟨X, by simpa [F] using congrArg flattenPinCoordinates hX⟩

theorem linearIndependent_pinRows_iff_pinRank [Fintype B] [Fintype E]
    (J : PairPinGraph B E) (p : E → Vec3) :
    LinearIndependent ℝ (pinRow J p) ↔ pinRank J p = 3 * Fintype.card E := by
  rw [linearIndependent_pinRows_iff_surjective, ← LinearMap.range_eq_top]
  constructor
  · intro h
    unfold pinRank
    rw [h]
    simp [Vec3, Module.finrank_pi_fintype, Nat.mul_comm]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa [pinRank, Vec3, Module.finrank_pi_fintype, Nat.mul_comm] using h

/-- Full generic row rank is equivalent to independence of the actual pin
rows at every placement attaining that rank. -/
theorem genericPinRank_eq_iff_pinRows_independent [Fintype B] [Fintype E]
    (J : PairPinGraph B E) :
    genericPinRank J = 3 * Fintype.card E ↔
      ∀ p : E → Vec3, pinRank J p = genericPinRank J →
        LinearIndependent ℝ (pinRow J p) := by
  constructor
  · intro h p hp
    exact (linearIndependent_pinRows_iff_pinRank J p).mpr (hp.trans h)
  · intro h
    obtain ⟨p, hp⟩ := genericPinRank_attained J
    exact hp.symm.trans ((linearIndependent_pinRows_iff_pinRank J p).mp (h p hp))

end Papers.Rigidity.PairPinGraph

end
end BundleSource0068

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0068/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0068.json"

section BundleSource0069
/- Source: Papers/RigidityPairPinOptimal.lean -/




@[expose] public section

/-!
# Optimal singleton partitions and independence of every pin row

An optimal block-constant kernel has the dimension of the whole actual
motion kernel. The inclusion is therefore onto. This proves that an
optimal partition can only identify bodies already in one rigid cluster;
when no bodies merge, its blocks are singletons. The simple-graph case
then has all three rows at every pin independent.
-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

open GenericPinIdeal
open MotionQuotient

variable {B E : Type} [Fintype B] [Fintype E] [Nonempty B]

/-- The no-merged-bodies hypothesis forces every optimal partition to be
injective, using actual maximum-rank real motions as its witnesses. -/
theorem optimal_partition_injective (J : PairPinGraph B E) (hNo : NoMergedBodies J)
    {t : ℕ} (π : B → Fin t) (hπ : Function.Surjective π)
    (hopt : 6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity π = genericRelativeDof J) :
    Function.Injective π := by
  classical
  obtain ⟨root⟩ := ‹Nonempty B›
  intro u v huv
  by_contra hne
  obtain ⟨p, hp, X, hX, hXne⟩ := hNo u v hne
  have hfull := realGroundedKernel_finrank_eq_genericRelativeDof J root p hp
  have hlower := J.toBodyPinIncidence.partitionDefect_le_groundedBlockKernel_finrank π p (π root)
  change 6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity π ≤
    Module.finrank ℝ
      (RB31E2E.groundedPinOperator (π root) (π ∘ J.left) (π ∘ J.right) p).ker at hlower
  rw [hopt] at hlower
  have hupper := groundedKernel_finrank_le_of_surjective π hπ root J.left J.right p
  have hdim : Module.finrank ℝ
      (RB31E2E.groundedPinOperator (π root) (π ∘ J.left) (π ∘ J.right) p).ker =
        Module.finrank ℝ (RB31E2E.groundedPinOperator root J.left J.right p).ker := by
    omega
  have hMotion : RB31E2E.IsTwistMotion J.left J.right p X := by
    apply (mem_motionSpace_iff J.left J.right p X).mp
    change X ∈ (motionOperator J.left J.right p).ker
    rwa [zheng_motionOperator_eq]
  exact hXne (equal_twists_of_groundedKernel_finrank_eq
    π hπ root J.left J.right p hdim u v huv X hMotion)

/-- The singleton partition attains the integer defect maximum whenever
no pair of distinct bodies belongs to one generic rigid cluster. -/
theorem maxPartitionDefect_eq_singleton_of_noMerged
    (J : PairPinGraph B E) (hNo : NoMergedBodies J) :
    maxPartitionDefect J = singletonPartitionDefect J := by
  classical
  obtain ⟨π, hmax⟩ := maxPartitionDefect_attained J
  let t := (Finset.univ.image π).card
  obtain ⟨σ, hσ, hcap⟩ := normalize_partition_labelling J π
  have htpos : 0 < t := by
    exact Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hdimension := pairPin_defect_dimension J
  have hopt : 6 * (t - 1) - J.toBodyPinIncidence.partitionCapacity σ = genericRelativeDof J := by
    have hm := hmax
    rw [labelledPartitionDefect, ← hcap, partitionCapacity_eq_incidenceCapacity] at hm
    change 6 * ((t : ℤ) - 1) -
      (J.toBodyPinIncidence.partitionCapacity σ : ℤ) = maxPartitionDefect J at hm
    omega
  have hσinj := optimal_partition_injective J hNo σ hσ hopt
  let e : B ≃ Fin t := Equiv.ofBijective σ ⟨hσinj, hσ⟩
  have ht : t = Fintype.card B := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  have hcapSingleton : partitionCapacity J σ =
      partitionCapacity J (Fintype.equivFin B) := by
    rw [partitionCapacity_eq_incidenceCapacity, partitionCapacity_eq_incidenceCapacity]
    change J.toBodyPinIncidence.capacityOn (e ∘ (id : B → B)) =
      J.toBodyPinIncidence.capacityOn ((Fintype.equivFin B) ∘ (id : B → B))
    exact (J.toBodyPinIncidence.capacityOn_comp_equiv e (id : B → B)).trans
      (J.toBodyPinIncidence.capacityOn_comp_equiv (Fintype.equivFin B) (id : B → B)).symm
  have hm : maxPartitionDefect J = 6 * ((t : ℤ) - 1) -
      (partitionCapacity J σ : ℤ) := by
    rw [← hmax, labelledPartitionDefect, hcap]
  rw [ht, hcapSingleton] at hm
  rw [hm, singletonPartitionDefect, labelledPartitionDefect]
  simp only [Finset.image_univ_of_surjective (Fintype.equivFin B).surjective,
    Finset.card_univ, Fintype.card_fin]

/-- In a simple loopless pin graph each actual unordered body pair carries
one occurrence, whose literal capacity is three. -/
theorem singletonCapacity_eq_three_card_of_simple
    (J : PairPinGraph B E) (hSimple : IsSimple J) :
    partitionCapacity J (Fintype.equivFin B) = 3 * Fintype.card E := by
  classical
  let H := J.toBodyPinIncidence
  rw [partitionCapacity_eq_incidenceCapacity]
  change H.capacityOn ((Fintype.equivFin B) ∘ (id : B → B)) = _
  have hcap : H.capacityOn ((Fintype.equivFin B) ∘ (id : B → B)) =
      H.capacityOn (id : B → B) :=
    H.capacityOn_comp_equiv (Fintype.equivFin B) (id : B → B)
  rw [hcap, H.capacityOn_eq_sum_actualPairs]
  have hpairs : H.actualPairs (id : B → B) =
      Finset.univ.image (fun e : E => s(J.left e, J.right e)) := by
    apply Finset.filter_eq_self.mpr
    intro b hb
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hb
    change ¬ (s(J.left e, J.right e)).IsDiag
    simpa only [Sym2.mk_isDiag_iff] using J.loopless e
  rw [hpairs, Finset.sum_image]
  · have hmult (e : E) : H.bundleMultiplicityOn (id : B → B) s(J.left e, J.right e) = 1 := by
      unfold RB31E2E.BodyPinIncidence.bundleMultiplicityOn
      change (Finset.univ.filter fun a : E => s(J.left a, J.right a) =
        s(J.left e, J.right e)).card = 1
      have hset : (Finset.univ.filter fun a : E => s(J.left a, J.right a) =
          s(J.left e, J.right e)) = {e} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          hSimple.eq_iff, Finset.mem_singleton]
      rw [hset]
      simp
    simp only [hmult, RB31E2E.pinCapacity_one, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.mul_comm]
  · intro a ha b hb hab
    exact hSimple hab

end

end Papers.Rigidity.PairPinGraph

namespace Papers.Rigidity

noncomputable section

/-- The singleton-optimality clause of Theorem 5.1, with the original
integer expression and generic real motion dimension. -/
theorem pairPin_singleton_partition_optimal
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) :
    (J.genericRelativeDof : ℤ) = J.singletonPartitionDefect :=
  (pairPin_defect_dimension J).trans
    (PairPinGraph.maxPartitionDefect_eq_singleton_of_noMerged J hNo)

/-- Every pin contributes all three independent coordinate rows in the
simple, unmerged case. -/
theorem pairPin_simple_genericPinRank
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) (hSimple : J.IsSimple) :
    J.genericPinRank = 3 * Fintype.card E := by
  have h := pairPin_singleton_partition_optimal J hNo
  have hcap := PairPinGraph.singletonCapacity_eq_three_card_of_simple J hSimple
  have hrank := PairPinGraph.genericPinRank_add_six_le J
  simp only [PairPinGraph.singletonPartitionDefect, PairPinGraph.labelledPartitionDefect,
    Finset.image_univ_of_surjective (Fintype.equivFin B).surjective,
    Finset.card_univ, Fintype.card_fin, hcap, PairPinGraph.genericRelativeDof] at h
  omega

/-- Literal linear independence, rather than a numerical substitute, of
the three occurrence-level rows at every maximum-rank real placement. -/
theorem pairPin_simple_pinRows_independent
    {B E : Type} [Fintype B] [Fintype E] [Nonempty B]
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) (hSimple : J.IsSimple)
    (p : E → Vec3) (hp : J.pinRank p = J.genericPinRank) :
    LinearIndependent ℝ (J.pinRow p) := by
  apply (PairPinGraph.linearIndependent_pinRows_iff_pinRank J p).mpr
  exact hp.trans (pairPin_simple_genericPinRank J hNo hSimple)

/-- All three clauses of Theorem 5.1 in the original paper-facing target. -/
theorem pairPin_defect_theorem : PairPinDefectClaim := by
  intro B E _ _ _ J
  exact ⟨pairPin_defect_dimension J, fun hNo =>
    ⟨pairPin_singleton_partition_optimal J hNo, fun hs => pairPin_simple_genericPinRank J hNo hs⟩⟩

end

end Papers.Rigidity

end
end BundleSource0069

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0069/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0069.json"

section BundleSource0070
/- Source: Papers/RigidityPairPinAlgebraicGeneric.lean -/




@[expose] public section

/-!
# The defect theorem at ordinary algebraically generic real pins

The numerical generic rank was defined as an attained maximum. This
module connects it directly to the conventional meaning of generic
coordinates: algebraic independence of all three coordinates of every
original pin occurrence over the rationals. The conclusion concerns the
actual quotient of the actual real compatibility kernel by common
Euclidean twists.
-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

open RB31E2E.GroundedTwistPolynomial
open GenericPinIdeal

variable {B E : Type} [Fintype B] [Fintype E] [Nonempty B]

/-- Algebraically independent pin coordinates attain the maximum real
rank of the original occurrence-level compatibility operator. -/
theorem pinRank_eq_generic_of_algebraicIndependent
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    pinRank J p = genericPinRank J := by
  classical
  obtain ⟨root⟩ := ‹Nonempty B›
  have hinj : Function.Injective
      (MvPolynomial.eval₂Hom (Rat.castHom ℝ) (assignmentOfPins p)) := by
    intro a b hab
    apply hp
    exact hab
  have h := PolynomialRank.realMatrix_rank_eq_generic_of_eval_injective
    (rationalMotionMatrix root J.left J.right) (assignmentOfPins p) hinj
  rw [realMatrix_rationalMotionMatrix, genericMatrix_rationalMotionMatrix,
    pinsOfAssignment_assignmentOfPins] at h
  rw [pinRank_eq_groundedMatrix_rank J root p,
    genericPinRank_eq_genericMotionMatrix_rank J root]
  exact h

/-- Theorem 5.1 in the conventional algebraically generic real-coordinate
form, with its quotient space and integer maximum both retained. -/
theorem relativeMotionSpace_finrank_eq_defect_of_algebraicIndependent
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = maxPartitionDefect J := by
  rw [← genericRelativeDof_eq_finrank_quotient J p
    (pinRank_eq_generic_of_algebraicIndependent J p hp)]
  exact pairPin_defect_dimension J

/-- In the simple, unmerged case the actual three coordinate rows per
pin are independent at every algebraically generic real placement. -/
theorem pinRows_independent_of_algebraicIndependent
    (J : PairPinGraph B E) (hNo : J.NoMergedBodies) (hSimple : J.IsSimple)
    (p : E → Vec3) (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    LinearIndependent ℝ (J.pinRow p) :=
  pairPin_simple_pinRows_independent J hNo hSimple p
    (pinRank_eq_generic_of_algebraicIndependent J p hp)

/-- At the specified placement, no pair of distinct bodies has identical
twists in every actual compatible motion. This is the direct
configuration-level meaning of the paper's rigid-cluster hypothesis. -/
def NoMergedAt (J : PairPinGraph B E) (p : E → Vec3) : Prop :=
  ∀ u v : B, u ≠ v → ∃ X : B → Twist,
    X ∈ (compatibilityOperator J p).ker ∧ X u ≠ X v

theorem noMergedBodies_of_algebraicIndependent
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) (hNo : NoMergedAt J p) :
    NoMergedBodies J := by
  intro u v huv
  exact ⟨p, pinRank_eq_generic_of_algebraicIndependent J p hp, hNo u v huv⟩

/-- All three assertions of Theorem 5.1 stated directly at an ordinary
algebraically generic real pin configuration. The first dimension is
that of the literal quotient by common twists; the last conclusion is
linear independence of the literal occurrence-level rows. -/
theorem defect_theorem_at_algebraicallyGeneric_pins
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : AlgebraicIndependent ℚ (assignmentOfPins p)) :
    (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = maxPartitionDefect J ∧
      (NoMergedAt J p →
        (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = singletonPartitionDefect J ∧
          (IsSimple J → LinearIndependent ℝ (pinRow J p))) := by
  refine ⟨relativeMotionSpace_finrank_eq_defect_of_algebraicIndependent J p hp, ?_⟩
  intro hNo
  have hglobal := noMergedBodies_of_algebraicIndependent J p hp hNo
  constructor
  · rw [← genericRelativeDof_eq_finrank_quotient J p
      (pinRank_eq_generic_of_algebraicIndependent J p hp)]
    exact pairPin_singleton_partition_optimal J hglobal
  · intro hSimple
    exact pinRows_independent_of_algebraicIndependent J hglobal hSimple p hp

end

end Papers.Rigidity.PairPinGraph

end
end BundleSource0070

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0070/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0070.json"

section BundleSource0071
/- Source: Papers/RigidityAuditPairPin.lean -/



/-!
# Final pair-pin theorem statement and axiom audit

This file is a verification gate. It must finish under the pinned ordinary
Lean compiler before any of the displayed terms is reported as verified.
The source audit is complementary and is not a substitute for this gate.
-/

#check Papers.Rigidity.pairPin_defect_theorem
#check Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins

#print axioms Papers.Rigidity.pairPin_defect_theorem
#print axioms Papers.Rigidity.pairPin_defect_dimension
#print axioms Papers.Rigidity.pairPin_singleton_partition_optimal
#print axioms Papers.Rigidity.pairPin_simple_pinRows_independent
#print axioms Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins
#print axioms Papers.Rigidity.GenericPinIdeal.genericGroundedKernel_finrank_eq_partitionDefectMaximum
#print axioms Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse
#print axioms Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard
#print axioms Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank

end BundleSource0071

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0071/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0071.json"

section BundleSource0072
/- Source: Papers/RigidityPairPinMaximalRank.lean -/



@[expose] public section

/-!
# The pair-pin defect theorem at every maximum-rank real placement

The numerical generic rank is the attained maximum of the actual real
compatibility operator. Therefore its dimension formula applies to every
placement attaining that rank, without an algebraic-independence premise.
The optional no-merger hypothesis below is tested in the actual compatible
motion kernel at the specified placement.

-/

namespace Papers.Rigidity.PairPinGraph

noncomputable section

variable {B E : Type} [Fintype B] [Fintype E] [Nonempty B]

/-- Literal separation at any maximum-rank placement supplies the witnesses
in the placement-independent generic no-merger hypothesis. -/
theorem noMergedBodies_of_maximalRank
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : pinRank J p = genericPinRank J) (hNo : NoMergedAt J p) :
    NoMergedBodies J := by
  intro u v huv
  exact ⟨p, hp, hNo u v huv⟩

/-- Every maximum-rank real pin placement has the full integer partition
defect. Under literal no-merger at that placement, the singleton partition
is optimal and every coordinate pin row is independent when the graph is
simple. No algebraic-independence hypothesis is needed. -/
theorem defect_at_maximal_rank_pins
    (J : PairPinGraph B E) (p : E → Vec3)
    (hp : pinRank J p = genericPinRank J) :
    (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = maxPartitionDefect J ∧
      (NoMergedAt J p →
        (Module.finrank ℝ (RelativeMotionSpace J p) : ℤ) = singletonPartitionDefect J ∧
          (IsSimple J → LinearIndependent ℝ (pinRow J p))) := by
  constructor
  · rw [← genericRelativeDof_eq_finrank_quotient J p hp]
    exact pairPin_defect_dimension J
  · intro hNo
    have hglobal := noMergedBodies_of_maximalRank J p hp hNo
    constructor
    · rw [← genericRelativeDof_eq_finrank_quotient J p hp]
      exact pairPin_singleton_partition_optimal J hglobal
    · intro hSimple
      exact pairPin_simple_pinRows_independent J hglobal hSimple p hp

end

end Papers.Rigidity.PairPinGraph

end
end BundleSource0072

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0072/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0072.json"

section BundleSource0073
/- Source: Papers/RigidityAuditMaximalRank.lean -/




/-!
This audit entry point is intended for the complete consolidated clean-build
closure, where all project proof bodies are present. It is not evidence of
verification until that build and the emitted audit both succeed.
-/

#check Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins
#print axioms Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins

#export_proof_audit Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins to ".lake/reports/audit/compiled_Papers_Rigidity_PairPinGraph_defect_at_maximal_rank_pins.json"

end BundleSource0073

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined02/block_0073/Consolidated/RigidityCombined02.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined02/checkpoint_0073.json"

