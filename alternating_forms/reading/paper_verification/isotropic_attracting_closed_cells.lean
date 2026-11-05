module

public import PaperVerification.IsotropicAttractingFiltrationOver

/-!
# The affine strata are closed in genuine ambient open subsets

This file supplies the geometry needed by both Chow localization and the
ordinary singular Thom sequence.  Consecutive projective stages are actual
closed complements.  Reversing the filtration realizes each nonempty affine
cell as a genuine closed immersion into an open subset of the original
smooth common-isotropic scheme.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PaperVerification.AlternatingForms

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

theorem filtrationInclusion_range {E F : Set (PluckerIndex (t+2) n)}
    (hEF : E ⊆ F) (c₁ c₂ : ℕ) (x : filtrationScheme (K := K) E c₁ c₂) :
    x ∈ Set.range (filtrationInclusion hEF c₁ c₂) ↔
      ∀ I ∈ F, Ideal.Quotient.mk (filtrationIdeal E c₁ c₂) (X I)
        ∈ x.asHomogeneousIdeal.toIdeal := by
  have hr := HomogeneousQuotientProjective.quotientProjMap_range
    (filtrationIdeal (K := K) E c₁ c₂) (filtrationIdeal (K := K) F c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂) (filtrationIdeal_isHomogeneous F c₁ c₂)
    (filtrationIdeal_mono hEF c₁ c₂) x
  refine hr.trans ?_
  rw [filtrationIdeal, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨_,h⟩ I hI
    exact h ⟨I,hI,rfl⟩
  · intro h
    constructor
    · intro q hq
      change Ideal.Quotient.mk (filtrationIdeal (K := K) E c₁ c₂) q ∈ x.asHomogeneousIdeal.toIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (show q ∈ filtrationIdeal E c₁ c₂ from Ideal.mem_sup_left hq)]
      exact Ideal.zero_mem _
    · rintro _ ⟨I,hI,rfl⟩
      exact h I hI

/-- The actual closed immersion of the next homogeneous stage. -/
def orderedFiltrationInclusion (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) (pivotPrefix (t+2) n (i.val+1)) c₁ c₂ ⟶
      filtrationScheme (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ :=
  filtrationInclusion (pivotPrefix_mono (t+2) n (Nat.le_succ i.val)) c₁ c₂

instance orderedFiltrationInclusion_isClosedImmersion
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosedImmersion (orderedFiltrationInclusion (K := K) i c₁ c₂) :=
  inferInstanceAs (IsClosedImmersion (filtrationInclusion _ _ _))

/-- Inside the current stage, the next stage is exactly the vanishing
locus of the current pivot coordinate. -/
theorem orderedFiltrationInclusion_range (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ)
    (x : filtrationScheme (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂) :
    x ∈ Set.range (orderedFiltrationInclusion i c₁ c₂) ↔
      Ideal.Quotient.mk (filtrationIdeal (pivotPrefix (t+2) n i.val) c₁ c₂)
        (X (weightOrderedPivots (t+2) n i)) ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [orderedFiltrationInclusion, filtrationInclusion_range, pivotPrefix_successor]
  constructor
  · intro h
    exact h _ (Set.mem_insert _ _)
  · intro hp I hI
    rcases Set.mem_insert_iff.mp hI with rfl | hI
    · exact hp
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (show X I ∈ filtrationIdeal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ from
          (show Ideal.span (X '' pivotPrefix (t+2) n i.val) ≤
            filtrationIdeal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ from le_sup_right)
              (Ideal.subset_span ⟨I,hI,rfl⟩))]
      exact Ideal.zero_mem _

/-- The exact closed/open complement assertion used by the genuine Chow
localization theorem, with the actual stage and cell morphisms. -/
theorem orderedFiltration_closed_open_complement
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    Set.range (orderedFiltrationInclusion (K := K) i c₁ c₂) =
      (Set.range (filtrationChart (K := K) (pivotPrefix (t+2) n i.val)
        (weightOrderedPivots (t+2) n i) c₁ c₂).ι)ᶜ := by
  ext x
  rw [orderedFiltrationInclusion_range, Scheme.Opens.range_ι]
  change _ ↔ ¬ ¬ _
  exact not_not.symm

/-- The reversed filtration consists of actual opens of the original
projective scheme. -/
def orderedComplement (m : ℕ) (c₁ c₂ : ℕ) :
    (Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))).Opens :=
  ⟨(Set.range (filtrationToOriginal (K := K) (pivotPrefix (t+2) n m) c₁ c₂))ᶜ,
    (isClosed_filtration_image _ _ _).isOpen_compl⟩

theorem orderedComplement_mono (c₁ c₂ : ℕ) :
    Monotone (fun m => orderedComplement (K := K) (n := n) (t := t) m c₁ c₂) := by
  intro a b hab
  exact Set.compl_subset_compl.mpr (ordered_filtration_antitone c₁ c₂ hab)

theorem orderedComplement_zero (c₁ c₂ : ℕ) :
    orderedComplement (K := K) (n := n) (t := t) 0 c₁ c₂ = ⊥ := by
  apply TopologicalSpace.Opens.ext
  change (Set.range (filtrationToOriginal (K := K) (pivotPrefix (t+2) n 0) c₁ c₂))ᶜ = ∅
  rw [filtration_image_zero, Set.compl_univ]

theorem orderedComplement_final (c₁ c₂ : ℕ) :
    orderedComplement (K := K) (n := n) (t := t) (pivotCount (t+2) n) c₁ c₂ = ⊤ := by
  apply TopologicalSpace.Opens.ext
  change (Set.range (filtrationToOriginal (K := K)
    (pivotPrefix (t+2) n (pivotCount (t+2) n)) c₁ c₂))ᶜ = Set.univ
  rw [filtration_image_final, Set.compl_empty]

/-- Pulling the next ambient complement back to the current closed stage
gives exactly its original pivot chart. -/
theorem orderedComplement_preimage (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationToOriginal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂ ⁻¹ᵁ
      orderedComplement (i.val+1) c₁ c₂ =
        filtrationChart (pivotPrefix (t+2) n i.val)
          (weightOrderedPivots (t+2) n i) c₁ c₂ := by
  ext x
  change ¬ (filtrationToOriginal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂) x ∈
    Set.range (filtrationToOriginal (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) ↔ _
  rw [ordered_filtration_successor_mem]
  have hx : (filtrationToOriginal (K := K) (pivotPrefix (t+2) n i.val) c₁ c₂) x ∈
      Set.range (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂) := ⟨x,rfl⟩
  simp only [hx, true_and]
  rfl

/-- The cell is a genuine closed subscheme of the next ambient open.
This is base change of the original projective closed immersion. -/
def orderedCellClosedMap (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    orderedFiltrationCell (K := K) i c₁ c₂ ⟶
      (orderedComplement (K := K) (n := n) (t := t) (i.val+1) c₁ c₂).toScheme :=
  (Scheme.isoOfEq _ (orderedComplement_preimage (K := K) i c₁ c₂)).inv ≫
    (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂ ∣_
      orderedComplement (i.val+1) c₁ c₂)

instance orderedCellClosedMap_isClosedImmersion
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosedImmersion (orderedCellClosedMap (K := K) i c₁ c₂) := by
  unfold orderedCellClosedMap
  infer_instance

theorem orderedCellClosedMap_comp_ι (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    orderedCellClosedMap (K := K) i c₁ c₂ ≫
      (orderedComplement (K := K) (n := n) (t := t) (i.val+1) c₁ c₂).ι =
        filtrationChartToOriginal (pivotPrefix (t+2) n i.val)
          (weightOrderedPivots (t+2) n i) c₁ c₂ := by
  rw [orderedCellClosedMap, Category.assoc, morphismRestrict_ι,
    Scheme.isoOfEq_inv_ι_assoc]
  rfl

end PaperVerification.IsotropicAttractingCharts
