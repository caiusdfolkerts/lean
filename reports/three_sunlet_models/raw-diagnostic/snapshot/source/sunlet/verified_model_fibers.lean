module
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Ring
public import sunlet.main_dimension
public import sunlet.verified_fiber_geometry
public import sunlet.verified_normalized_model

@[expose] public section
noncomputable section
set_option Elab.async false

#check "SUNLET_VerifiedModelFibers_IMPORTS_READY"

section Stage_RationalSubstitution



/-!
# Clearing coordinate denominators uniformly

The same numerator and denominator work over the ground field and a
specified extension field.  The denominator is proved nonzero whenever
the substituted coordinate denominators are nonzero.  Thus generic
identities can be specialized at every point of the relevant open set.
-/

noncomputable section

namespace Sunlet.RationalSubstitution

variable {k I J : Type*} [Field k]
  (num den : J → I)

def values {A : Type*} [Field A] (q : I → A) : J → A :=
  fun j => q (num j) / q (den j)

def Clears (A : Type*) [Field A] [Algebra k A]
    (P : MvPolynomial J k) (N D : MvPolynomial I k) : Prop :=
  ∀ q : I → A, (∀ j, q (den j) ≠ 0) →
    MvPolynomial.aeval q D ≠ 0 ∧
      MvPolynomial.aeval (values num den q) P * MvPolynomial.aeval q D =
        MvPolynomial.aeval q N

variable {A : Type*} [Field A] [Algebra k A]

theorem clears_C (c : k) :
    Clears num den A (MvPolynomial.C c) (MvPolynomial.C c) 1 := by
  intro q hq
  simp

theorem clears_add {P Q : MvPolynomial J k} {NP DP NQ DQ : MvPolynomial I k}
    (hp : Clears num den A P NP DP) (hq : Clears num den A Q NQ DQ) :
    Clears num den A (P + Q) (NP * DQ + NQ * DP) (DP * DQ) := by
  intro q hd
  obtain ⟨hDP, hP⟩ := hp q hd
  obtain ⟨hDQ, hQ⟩ := hq q hd
  refine ⟨by simpa only [map_mul] using mul_ne_zero hDP hDQ, ?_⟩
  simp only [map_add, map_mul]
  calc
    (MvPolynomial.aeval (values num den q) P + MvPolynomial.aeval (values num den q) Q) *
        (MvPolynomial.aeval q DP * MvPolynomial.aeval q DQ) =
      (MvPolynomial.aeval (values num den q) P * MvPolynomial.aeval q DP) *
          MvPolynomial.aeval q DQ +
        (MvPolynomial.aeval (values num den q) Q * MvPolynomial.aeval q DQ) *
          MvPolynomial.aeval q DP := by ring
    _ = _ := by rw [hP, hQ]

theorem clears_mul_X {P : MvPolynomial J k} {N D : MvPolynomial I k}
    (hp : Clears num den A P N D) (j : J) :
    Clears num den A (P * MvPolynomial.X j)
      (N * MvPolynomial.X (num j)) (D * MvPolynomial.X (den j)) := by
  intro q hd
  obtain ⟨hD, hP⟩ := hp q hd
  refine ⟨by simpa only [map_mul, MvPolynomial.aeval_X] using mul_ne_zero hD (hd j), ?_⟩
  simp only [map_mul, MvPolynomial.aeval_X, values]
  calc
    MvPolynomial.aeval (values num den q) P * (q (num j) / q (den j)) *
        (MvPolynomial.aeval q D * q (den j)) =
      (MvPolynomial.aeval (values num den q) P * MvPolynomial.aeval q D) *
        ((q (num j) / q (den j)) * q (den j)) := by ring
    _ = MvPolynomial.aeval q N * q (num j) := by rw [hP, div_mul_cancel₀ _ (hd j)]

/-- The formulas are chosen simultaneously for closed points and generic
points. Neither application introduces new denominator assumptions. -/
theorem exists_clears_two (A B : Type*) [Field A] [Field B]
    [Algebra k A] [Algebra k B] (P : MvPolynomial J k) :
    ∃ N D : MvPolynomial I k,
      Clears num den A P N D ∧ Clears num den B P N D := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨MvPolynomial.C c, 1, clears_C num den c, clears_C num den c⟩
  | add P Q hp hq =>
      obtain ⟨NP, DP, hpA, hpB⟩ := hp
      obtain ⟨NQ, DQ, hqA, hqB⟩ := hq
      exact ⟨NP * DQ + NQ * DP, DP * DQ,
        clears_add num den hpA hqA, clears_add num den hpB hqB⟩
  | mul_X P j hp =>
      obtain ⟨N, D, hpA, hpB⟩ := hp
      exact ⟨N * MvPolynomial.X (num j), D * MvPolynomial.X (den j),
        clears_mul_X num den hpA j, clears_mul_X num den hpB j⟩

end Sunlet.RationalSubstitution
end
end Stage_RationalSubstitution

#check "SUNLET_RationalSubstitution_READY"

section Stage_PolynomialPrincipalOpen



/-! Nonempty dense principal opens in the actual image of a polynomial map. -/

noncomputable section

namespace PolynomialImage

variable {k I S : Type*} [Field k] [Infinite k]
  (P : I → MvPolynomial S k) (D : MvPolynomial I k)

def principalOpen : Set (I → k) :=
  {x | x ∈ closure P ∧ MvPolynomial.aeval x D ≠ 0}

theorem principalOpen_vanishingIdeal (hD : D ∉ definingIdeal P) :
    MvPolynomial.vanishingIdeal k (principalOpen P D) = definingIdeal P := by
  apply le_antisymm
  · intro f hf
    have hprod : f * D ∈ definingIdeal P := by
      rw [← vanishingIdeal_imageClosure P]
      intro x hx
      rw [map_mul]
      by_cases h : MvPolynomial.aeval x D = 0
      · rw [h, mul_zero]
      · rw [hf x ⟨hx, h⟩, zero_mul]
    exact ((RingHom.ker_isPrime (comorphism P)).mem_or_mem hprod).resolve_right hD
  · intro f hf x hx
    exact hx.1 f hf

theorem principalOpen_dense (hD : D ∉ definingIdeal P) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k (principalOpen P D)) = closure P := by
  rw [principalOpen_vanishingIdeal P D hD]
  rfl

theorem principalOpen_nonempty (hD : D ∉ definingIdeal P) :
    (principalOpen P D).Nonempty := by
  by_contra h
  have he : principalOpen P D = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have ht : definingIdeal P = ⊤ := by
    rw [← principalOpen_vanishingIdeal P D hD, he, MvPolynomial.vanishingIdeal_empty]
  exact (RingHom.ker_isPrime (comorphism P)).ne_top ht

end PolynomialImage
end
end Stage_PolynomialPrincipalOpen

#check "SUNLET_PolynomialPrincipalOpen_READY"

section Stage_ModelFiberOpen



/-!
# The fiber open inside the original affine model

Every equation is interpreted through the original five-family polynomial
map.  The diagonal division is justified on a constructed nonempty dense
principal open.  Consequently the secant calculation covers a general
fiber of the actual model, including all its affine parameter points.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {K ι Ω : Type*} [Field K] [CharZero K]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

def offDiagonalNumeratorIndex (ax : L.NonidentityColor × Ω) : ι × Ω := (ax.1.val, ax.2)
def offDiagonalDenominatorIndex (ax : L.NonidentityColor × Ω) : ι × Ω :=
  (L.identity, L.nonidentityPerm ax.1 ax.2)

def offDiagonalRatios {A : Type*} [Field A] (q : ι × Ω → A) : L.NonidentityColor × Ω → A :=
  RationalSubstitution.values L.offDiagonalNumeratorIndex L.offDiagonalDenominatorIndex q

theorem generic_normalized_identity (b : Ω) :
    Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o) (L.identity, b) =
      RationalBaseChange.diagonal b := by
  simp [Normalization.parameterMap, Normalization.coordinate, genericNormalizedParameters]

theorem generic_normalized_nonidentity (a : L.NonidentityColor) (b : Ω) :
    Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o) (a.val, b) =
      RationalBaseChange.diagonal (L.nonidentityPerm a b) *
        L.normalizedSourceEmbedding o (genericCoordinates (k := K) o L.nonidentityPerm (a, b)) := by
  have h := congrFun (L.generic_normalized_coordinates (k := K) o) (Sum.inr (a, b))
  simpa only [Function.comp_apply, normalizedCoordinateIndex, Equiv.coe_fn_mk,
    RationalBaseChange.coordinates, normalizedSourceEmbedding, IsScalarTower.toAlgHom_apply] using h

theorem offDiagonalRatios_generic :
    L.offDiagonalRatios
      (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o)) =
      L.normalizedSourceEmbedding o ∘ genericCoordinates (k := K) o L.nonidentityPerm := by
  funext ax
  simp only [offDiagonalRatios, RationalSubstitution.values, offDiagonalNumeratorIndex,
    offDiagonalDenominatorIndex, L.generic_normalized_identity o,
    L.generic_normalized_nonidentity o, Function.comp_apply]
  exact mul_div_cancel_left₀ _ (RationalBaseChange.diagonal_ne_zero _)

theorem offDiagonalRatios_generic_aeval (P : MvPolynomial (L.NonidentityColor × Ω) K) :
    MvPolynomial.aeval (L.offDiagonalRatios
      (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o))) P =
      L.normalizedSourceEmbedding o
        (MvPolynomial.aeval (genericCoordinates (k := K) o L.nonidentityPerm) P) := by
  rw [L.offDiagonalRatios_generic o]
  exact (MvPolynomial.comp_aeval_apply _ (L.normalizedSourceEmbedding o) P).symm

/-- Every point of the original model with nonzero diagonal has its
off-diagonal ratios in the actual secant closure. -/
theorem ratios_mem_secantClosure (q : ι × Ω → K)
    (hq : q ∈ Sunlet.imageClosure L.perm) (hd : ∀ b, q (L.identity, b) ≠ 0) :
    L.offDiagonalRatios q ∈ secantClosure (k := K) o L.nonidentityPerm := by
  rw [secantClosure_eq_generic_zeroLocus]
  intro P hP
  obtain ⟨N, D, hK, hE⟩ := RationalSubstitution.exists_clears_two
    L.offDiagonalNumeratorIndex L.offDiagonalDenominatorIndex
    K (L.NormalizedSourceField (k := K) o) P
  let qg := Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o)
  have hgd : ∀ ax : L.NonidentityColor × Ω, qg (L.offDiagonalDenominatorIndex ax) ≠ 0 := by
    intro ax
    change Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o)
      (L.identity, L.nonidentityPerm ax.1 ax.2) ≠ 0
    rw [L.generic_normalized_identity o]
    exact RationalBaseChange.diagonal_ne_zero _
  have hNg : MvPolynomial.aeval qg N = 0 := by
    have h := (hE qg hgd).2
    change MvPolynomial.aeval (L.offDiagonalRatios qg) P * MvPolynomial.aeval qg D =
      MvPolynomial.aeval qg N at h
    rw [L.offDiagonalRatios_generic_aeval o] at h
    change MvPolynomial.aeval (genericCoordinates (k := K) o L.nonidentityPerm) P = 0 at hP
    rw [hP, map_zero, zero_mul] at h
    exact h.symm
  have hN : N ∈ PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) L.perm) :=
    (L.generic_normalized_equation_iff (k := K) o N).mp hNg
  have hNq := hq N hN
  obtain ⟨hDq, hrel⟩ := hK q (fun ax => hd (L.nonidentityPerm ax.1 ax.2))
  rw [hNq] at hrel
  exact (mul_eq_zero.mp hrel).resolve_right hDq

def diagonalProduct : MvPolynomial (ι × Ω) K :=
  ∏ b : Ω, MvPolynomial.X (L.identity, b)

theorem diagonalProduct_generic_ne :
    MvPolynomial.aeval
      (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o))
      (L.diagonalProduct (K := K)) ≠ 0 := by
  simp only [diagonalProduct, map_prod, MvPolynomial.aeval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  rw [L.generic_normalized_identity o]
  exact RationalBaseChange.diagonal_ne_zero _

theorem diagonal_ne_of_product_ne (q : ι × Ω → K)
    (h : MvPolynomial.aeval q (L.diagonalProduct (K := K)) ≠ 0) (b : Ω) :
    q (L.identity, b) ≠ 0 := by
  simp only [diagonalProduct, map_prod, MvPolynomial.aeval_X] at h
  exact (Finset.prod_ne_zero_iff.mp h) b (Finset.mem_univ b)

/-- Pullback of the constructed secant open is a genuine principal open
of the original affine model, and it is nonempty and dense there. -/
theorem exists_model_open_over_secant_open
    (P : MvPolynomial (L.NonidentityColor × Ω) K)
    (hP : MvPolynomial.aeval (genericCoordinates (k := K) o L.nonidentityPerm) P ≠ 0) :
    ∃ W : MvPolynomial (ι × Ω) K,
      W ∉ PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) L.perm) ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W,
        (∀ b, q (L.identity, b) ≠ 0) ∧
          L.offDiagonalRatios q ∈ principalOpen (k := K) o L.nonidentityPerm P := by
  obtain ⟨N, D, hK, hE⟩ := RationalSubstitution.exists_clears_two
    L.offDiagonalNumeratorIndex L.offDiagonalDenominatorIndex
    K (L.NormalizedSourceField (k := K) o) P
  let qg := Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o)
  have hgd : ∀ ax : L.NonidentityColor × Ω, qg (L.offDiagonalDenominatorIndex ax) ≠ 0 := by
    intro ax
    change Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := K) o)
      (L.identity, L.nonidentityPerm ax.1 ax.2) ≠ 0
    rw [L.generic_normalized_identity o]
    exact RationalBaseChange.diagonal_ne_zero _
  have hNg : MvPolynomial.aeval qg N ≠ 0 := by
    obtain ⟨hD, hrel⟩ := hE qg hgd
    rw [← hrel]
    apply mul_ne_zero _ hD
    change MvPolynomial.aeval (L.offDiagonalRatios qg) P ≠ 0
    rw [L.offDiagonalRatios_generic_aeval o]
    exact (map_ne_zero (L.normalizedSourceEmbedding (k := K) o)).mpr hP
  refine ⟨L.diagonalProduct * N, ?_, ?_⟩
  · intro hw
    have hz := (L.generic_normalized_equation_iff (k := K) o _).mpr hw
    rw [map_mul] at hz
    exact mul_ne_zero (L.diagonalProduct_generic_ne (K := K) o) hNg hz
  · intro q hq
    have hw := hq.2
    rw [map_mul] at hw
    have hd := L.diagonal_ne_of_product_ne q (mul_ne_zero_iff.mp hw).1
    refine ⟨hd, L.ratios_mem_secantClosure o q hq.1 hd, ?_⟩
    obtain ⟨hDq, hrel⟩ := hK q (fun ax => hd (L.nonidentityPerm ax.1 ax.2))
    intro hz
    change MvPolynomial.aeval (L.offDiagonalRatios q) P * MvPolynomial.aeval q D =
      MvPolynomial.aeval q N at hrel
    rw [hz, zero_mul] at hrel
    exact (mul_ne_zero_iff.mp hw).2 hrel.symm

theorem coordinatesOfDiagonal_ratios (q : ι × Ω → K)
    (hd : ∀ b, q (L.identity, b) ≠ 0) :
    L.coordinatesOfDiagonal (fun b => Units.mk0 (q (L.identity, b)) (hd b))
      (L.offDiagonalRatios q) = q := by
  funext ab
  rcases ab with ⟨a, b⟩
  by_cases ha : a = L.identity
  · subst a
    simp [coordinatesOfDiagonal]
  · simp only [coordinatesOfDiagonal, dif_neg ha, Units.val_mk0,
      offDiagonalRatios, RationalSubstitution.values, offDiagonalNumeratorIndex,
      offDiagonalDenominatorIndex]
    exact mul_div_cancel₀ _ (hd (L.perm a b))

/-- The whole original affine fiber over every point in a constructed
nonempty dense principal open. The discrete factor has exactly 2c²
elements; its continuous factor has the three unit gauges and one affine
coordinate specified in Theorem 4.2. -/
theorem model_general_normalized_fiber [IsAlgClosed K] (hm : 5 ≤ Fintype.card Ω) :
    ∃ W : MvPolynomial (ι × Ω) K,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W).Nonempty ∧
      MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W)) =
          Sunlet.imageClosure L.perm ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W,
        (∀ b, q (L.identity, b) ≠ 0) ∧
        Nonempty (NormalizationFibers.NormalizedFiber L.identity o L.perm q ≃
          L.DiscreteFiber (K := K) o) := by
  obtain ⟨P, hP, hnonempty, hdense, hfiber⟩ := L.general_normalized_fiber_open_chart (K := K) o hm
  obtain ⟨W, hW, hchart⟩ := L.exists_model_open_over_secant_open o P hP
  refine ⟨W, PolynomialImage.principalOpen_nonempty _ _ hW,
    PolynomialImage.principalOpen_dense _ _ hW, ?_⟩
  intro q hq
  obtain ⟨hd, hz⟩ := hchart q hq
  refine ⟨hd, ?_⟩
  have h := hfiber (L.offDiagonalRatios q) hz
    (fun b => Units.mk0 (q (L.identity, b)) (hd b))
  simpa only [L.coordinatesOfDiagonal_ratios q hd] using h

/-- The same open gives the full original affine fiber, with its explicit
finite factor and the four continuous gauge parameters. -/
theorem model_general_affine_fiber [IsAlgClosed K] (hm : 5 ≤ Fintype.card Ω) :
    ∃ W : MvPolynomial (ι × Ω) K,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W).Nonempty ∧
      MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W)) =
          Sunlet.imageClosure L.perm ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W,
        Nonempty (NormalizationFibers.AffineFiber L.perm q ≃
          L.DiscreteFiber (K := K) o × NormalizationFibers.Gauges (R := K)) := by
  obtain ⟨W, hn, hd, hf⟩ := L.model_general_normalized_fiber (K := K) o hm
  refine ⟨W, hn, hd, ?_⟩
  intro q hq
  obtain ⟨hdiag, ⟨e⟩⟩ := hf q hq
  exact ⟨(NormalizationFibers.fiberEquiv L.identity o L.perm L.normalized q
    (fun b => isUnit_iff_ne_zero.mpr (hdiag b))).trans
      (Equiv.prodCongr e (Equiv.refl _))⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_ModelFiberOpen

#check "SUNLET_ModelFiberOpen_READY"

section Stage_ModelFiberVariety



/-!
# The general fiber as a disjoint union of algebraic varieties

The conclusion supplies closed component equations in the original
affine parameter coordinates, proves disjointness and exhaustive coverage,
and gives polynomial inverse maps between each component and three
multiplicative groups times one affine line.  It is stronger than an
abstract bijection of complex points.
-/

noncomputable section

namespace Sunlet.NormalizedLatinSystem

variable {K ι Ω : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

/-- The general-fiber assertion of Theorem 4.2, expressed by actual
polynomial isomorphisms and a finite closed disjoint decomposition of the
whole original affine fiber.  The seven-coordinate gauge variety has
three equations `x*y=1` and one free coordinate. -/
theorem paper_theorem_4_2_algebraic_fibers (hm : 5 ≤ Fintype.card Ω) :
    Nat.card (L.DiscreteFiber (K := K) o) = 2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 ∧
    ∃ W : MvPolynomial (ι × Ω) K,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W).Nonempty ∧
      MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W)) =
          Sunlet.imageClosure L.perm ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W,
        ∃ C : L.DiscreteFiber (K := K) o → Set (ParamVar ι Ω → K),
          (∀ j, ∃ A : Ideal (MvPolynomial (ParamVar ι Ω) K), C j = MvPolynomial.zeroLocus K A) ∧
          Pairwise (fun i j => Disjoint (C i) (C j)) ∧
          (⋃ j, C j) = FiberAlgebraic.affineFiberSet L.perm q ∧
          ∀ j, Nonempty (AlgebraicSets.PolynomialEquiv (C j) (FiberAlgebraic.gaugeSpace (K := K))) := by
  refine ⟨L.discreteFiber_card (K := K) o, ?_⟩
  obtain ⟨W, hn, hd, hf⟩ := L.model_general_normalized_fiber (K := K) o hm
  refine ⟨W, hn, hd, ?_⟩
  intro q hq
  obtain ⟨hdiag, ⟨e⟩⟩ := hf q hq
  let C : L.DiscreteFiber (K := K) o → Set (ParamVar ι Ω → K) :=
    fun j => FiberAlgebraic.component L.identity o (e.symm j).val
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro j
    exact FiberAlgebraic.component_isAlgebraic L.identity o (e.symm j).val
  · intro i j hij
    apply FiberAlgebraic.components_disjoint L.identity o
    intro h
    apply hij
    apply e.symm.injective
    exact Subtype.ext h
  · have hc := FiberAlgebraic.components_cover L.identity o L.perm L.normalized q
        (fun b => isUnit_iff_ne_zero.mpr (hdiag b))
    rw [← hc]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨e.symm j, hj⟩
    · rintro ⟨p, hp⟩
      refine ⟨e p, ?_⟩
      simpa only [C, e.symm_apply_apply] using hp
  · intro j
    exact ⟨FiberAlgebraic.componentEquiv L.identity o (e.symm j).val⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_ModelFiberVariety

#check "SUNLET_ModelFiberVariety_READY"

section Stage_SixFamilyGenericFiber



/-!
# General fibers before absorption of the sixth edge family

The existing nonempty dense model open is intersected with one coordinate
hyperplane complement per color.  These intersections are nonempty:
the full model contains the point with every output coordinate equal to
one, and its defining ideal is prime.  Thus all additional torus factors
are forced by output conditions on an explicitly specified dense open.
-/

noncomputable section

namespace Sunlet.SixFamilyGenericFiber

variable {K ι Ω : Type*} [Field K] [Infinite K] [Fintype ι]
  (π : ι → Equiv.Perm Ω) (o : Ω)

def rowProduct : MvPolynomial (ι × Ω) K := ∏ a : ι, MvPolynomial.X (a, o)

theorem rowProduct_not_mem :
    rowProduct (K := K) (ι := ι) o ∉ PolynomialImage.definingIdeal
      (Sunlet.coordinatePolynomial (K := K) π) := by
  let p : Sunlet.Parameters K ι Ω :=
    {s := fun _ => 1, t := fun _ => 1, h := fun _ => 1,
      u := fun _ => 1, v := fun _ => 0}
  have hp (ab : ι × Ω) : Sunlet.parameterMap π p ab = 1 := by
    simp [Sunlet.parameterMap, Sunlet.coordinate, p]
  have he : MvPolynomial.aeval p.toCoordinates
      (PolynomialImage.comorphism (Sunlet.coordinatePolynomial (K := K) π)
        (rowProduct (K := K) (ι := ι) o)) = 1 := by
    simp [rowProduct, PolynomialImage.comorphism, map_prod, Sunlet.aeval_coordinatePolynomial, hp]
  intro h
  change PolynomialImage.comorphism (Sunlet.coordinatePolynomial (K := K) π)
    (rowProduct (K := K) (ι := ι) o) = 0 at h
  rw [h, map_zero] at he
  exact zero_ne_one he

theorem rowProduct_evaluate (q : ι × Ω → K) :
    MvPolynomial.aeval q (rowProduct (K := K) (ι := ι) o) = ∏ a : ι, q (a, o) := by
  simp [rowProduct, map_prod]

theorem strengthen_open (W : MvPolynomial (ι × Ω) K)
    (hn : (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) π) W).Nonempty) :
    (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) π)
      (W * rowProduct (K := K) (ι := ι) o)).Nonempty ∧
    MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) π)
        (W * rowProduct (K := K) (ι := ι) o))) = Sunlet.imageClosure π ∧
    ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) π)
      (W * rowProduct (K := K) (ι := ι) o),
      q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) π) W ∧
        ∀ a, q (a, o) ≠ 0 := by
  have hW : W ∉ PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) π) := by
    intro h
    obtain ⟨q, hq⟩ := hn
    exact hq.2 (hq.1 W h)
  have hprod : W * rowProduct (K := K) (ι := ι) o ∉
      PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) π) := by
    intro h
    rcases (RingHom.ker_isPrime
      (PolynomialImage.comorphism (Sunlet.coordinatePolynomial (K := K) π))).mem_or_mem h with h | h
    · exact hW h
    · exact rowProduct_not_mem π o h
  refine ⟨PolynomialImage.principalOpen_nonempty _ _ hprod,
    PolynomialImage.principalOpen_dense _ _ hprod, ?_⟩
  intro q hq
  have h := hq.2
  rw [map_mul, rowProduct_evaluate] at h
  have hh := mul_ne_zero_iff.mp h
  exact ⟨⟨hq.1, hh.1⟩,
    fun a => Finset.prod_ne_zero_iff.mp hh.2 a (Finset.mem_univ a)⟩

end Sunlet.SixFamilyGenericFiber

namespace Sunlet.NormalizedLatinSystem

variable {K ι Ω : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

/-- The six-family version of the general-fiber consequence: the entire
affine fiber has `2c²` disjoint closed components, each polynomially
isomorphic to `(K*)^(3 + card ι) × K`, with every unit inverse represented
by its own affine coordinate and its equation `x*y=1`. -/
theorem six_family_general_algebraic_fiber (hm : 5 ≤ Fintype.card Ω) :
    Nat.card (L.DiscreteFiber (K := K) o) = 2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 ∧
    ∃ W : MvPolynomial (ι × Ω) K,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W).Nonempty ∧
      MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W)) =
          Sunlet.imageClosure L.perm ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W,
        (∀ a, q (a, o) ≠ 0) ∧
        ∃ C : L.DiscreteFiber (K := K) o → Set (SixFamilyFibers.ParamVar ι Ω → K),
          (∀ j, ∃ A : Ideal (MvPolynomial (SixFamilyFibers.ParamVar ι Ω) K),
            C j = MvPolynomial.zeroLocus K A) ∧
          Pairwise (fun i j => Disjoint (C i) (C j)) ∧
          (⋃ j, C j) = SixFamilyAlgebraic.affineFiberSet L.perm q ∧
          ∀ j, Nonempty (AlgebraicSets.PolynomialEquiv (C j)
            (SixFamilyAlgebraic.gaugeSpace (K := K) (ι := ι))) := by
  refine ⟨L.discreteFiber_card (K := K) o, ?_⟩
  obtain ⟨W, hn, hd, hf⟩ := L.model_general_normalized_fiber (K := K) o hm
  obtain ⟨hnew, hdense, hrefine⟩ := SixFamilyGenericFiber.strengthen_open L.perm o W hn
  refine ⟨W * SixFamilyGenericFiber.rowProduct o, hnew, hdense, ?_⟩
  intro q hq
  obtain ⟨hold, hrows⟩ := hrefine q hq
  obtain ⟨hdiag, ⟨f⟩⟩ := hf q hold
  let C : L.DiscreteFiber (K := K) o → Set (SixFamilyFibers.ParamVar ι Ω → K) :=
    fun j => SixFamilyAlgebraic.component L.identity o L.perm q (fun _ => o) (f.symm j)
  refine ⟨hrows, C, ?_, ?_, ?_, ?_⟩
  · intro j
    exact SixFamilyAlgebraic.component_isAlgebraic L.identity o L.perm q (fun _ => o) (f.symm j)
  · intro i j hij
    apply SixFamilyAlgebraic.components_disjoint L.identity o L.perm L.normalized q
      (fun _ => o) hrows
    exact fun h => hij (f.symm.injective h)
  · have hc := SixFamilyAlgebraic.components_cover L.identity o L.perm L.normalized q
        (fun _ => o) hrows (fun b => isUnit_iff_ne_zero.mpr (hdiag b))
    rw [← hc]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨f.symm j, hj⟩
    · rintro ⟨p, hp⟩
      refine ⟨f p, ?_⟩
      simpa only [C, f.symm_apply_apply] using hp
  · intro j
    exact ⟨SixFamilyAlgebraic.componentEquiv L.identity o L.perm L.normalized q
      (fun _ => o) hrows (f.symm j)⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_SixFamilyGenericFiber

#check "SUNLET_SixFamilyGenericFiber_READY"

section Stage_SixFamilyLiteral



/-!
# Six-family fiber components in the manuscript's original variables

This module removes the remaining notational reindexing.  Both the change
of coordinates and its inverse are coordinate permutations, hence literal
polynomial maps.  The endpoint uses the affine space indexed by `Fin 6 × G`
and the exact six-family polynomial from `GroupCoordinates.coordinate`.
-/

noncomputable section

namespace Sunlet.SixFamilyLiteral

open AlgebraicSets

variable {K G : Type*} [Field K] [AddCommGroup G]

def variableEquiv : (Fin 6 × G) ≃ SixFamilyFibers.ParamVar G G where
  toFun ia := match ia.1 with
    | 0 => .inl ia.2
    | 1 => .inr (.s ia.2)
    | 2 => .inr (.t (-ia.2))
    | 3 => .inr (.h ia.2)
    | 4 => .inr (.u ia.2)
    | _ => .inr (.v ia.2)
  invFun j := match j with
    | .inl a => (0, a)
    | .inr (.s a) => (1, a)
    | .inr (.t a) => (2, -a)
    | .inr (.h a) => (3, a)
    | .inr (.u a) => (4, a)
    | .inr (.v a) => (5, a)
  left_inv ia := by
    rcases ia with ⟨i, a⟩
    fin_cases i <;> simp
  right_inv j := by
    cases j with
    | inl a => rfl
    | inr j => cases j <;> simp

def forwardPolynomials : SixFamilyFibers.ParamVar G G → MvPolynomial (Fin 6 × G) K :=
  fun j => MvPolynomial.X (variableEquiv.symm j)

def inversePolynomials : (Fin 6 × G) → MvPolynomial (SixFamilyFibers.ParamVar G G) K :=
  fun i => MvPolynomial.X (variableEquiv i)

def pullbackSet (C : Set (SixFamilyFibers.ParamVar G G → K)) : Set ((Fin 6 × G) → K) :=
  {x | polynomialMap forwardPolynomials x ∈ C}

theorem polynomial_left_inverse (x : (Fin 6 × G) → K) :
    polynomialMap inversePolynomials (polynomialMap forwardPolynomials x) = x := by
  funext i
  simp [polynomialMap, forwardPolynomials, inversePolynomials]

theorem polynomial_right_inverse (x : SixFamilyFibers.ParamVar G G → K) :
    polynomialMap forwardPolynomials (polynomialMap inversePolynomials x) = x := by
  funext i
  simp [polynomialMap, forwardPolynomials, inversePolynomials]

def pullbackEquiv (C : Set (SixFamilyFibers.ParamVar G G → K)) :
    PolynomialEquiv (pullbackSet C) C where
  forward := forwardPolynomials
  inverse := inversePolynomials
  forward_mem _ hx := hx
  inverse_mem x hx := by
    change polynomialMap forwardPolynomials (polynomialMap inversePolynomials x) ∈ C
    rw [polynomial_right_inverse]
    exact hx
  left_inverse x _ := polynomial_left_inverse x
  right_inverse x _ := polynomial_right_inverse x

theorem pullback_eq_retraction (C : Set (SixFamilyFibers.ParamVar G G → K)) :
    pullbackSet C = retractionSet forwardPolynomials inversePolynomials C := by
  ext x
  exact ⟨fun hx => ⟨hx, polynomial_left_inverse x⟩, fun hx => hx.1⟩

theorem pullback_isAlgebraic (C : Set (SixFamilyFibers.ParamVar G G → K))
    (hC : ∃ A : Ideal (MvPolynomial (SixFamilyFibers.ParamVar G G) K),
      C = MvPolynomial.zeroLocus K A) :
    ∃ A : Ideal (MvPolynomial (Fin 6 × G) K), pullbackSet C = MvPolynomial.zeroLocus K A := by
  obtain ⟨A, hA⟩ := hC
  refine ⟨retractionIdeal forwardPolynomials inversePolynomials A, ?_⟩
  rw [pullback_eq_retraction, hA, retractionSet_eq_zeroLocus]

theorem pullback_disjoint (C D : Set (SixFamilyFibers.ParamVar G G → K)) (h : Disjoint C D) :
    Disjoint (pullbackSet C) (pullbackSet D) := by
  rw [Set.disjoint_left] at h ⊢
  exact fun x hx hd => h (a := polynomialMap forwardPolynomials x) hx hd

theorem ofCoordinates_forward (x : (Fin 6 × G) → K) :
    SixFamilyFibers.Parameters.ofCoordinates (polynomialMap forwardPolynomials x) =
      SixFamilyFibers.groupParametersEquiv (fun i a => x (i, a)) := by
  simp [SixFamilyFibers.Parameters.ofCoordinates, polynomialMap, forwardPolynomials,
    variableEquiv, SixFamilyFibers.groupParametersEquiv, Sunlet.Parameters.ofCoordinates]

def affineFiberSet (q : G × G → K) : Set ((Fin 6 × G) → K) :=
  {x | GroupCoordinates.parameterMap (fun i a => x (i, a)) = q}

def coordinatePolynomial (ab : G × G) : MvPolynomial (Fin 6 × G) K :=
  MvPolynomial.X (0, ab.1) * MvPolynomial.X (1, ab.2) *
    MvPolynomial.X (2, -(ab.1 + ab.2)) *
      (MvPolynomial.X (3, ab.1 + ab.2) * MvPolynomial.X (4, ab.1) +
        MvPolynomial.X (3, ab.2) * MvPolynomial.X (5, ab.1))

theorem aeval_coordinatePolynomial (x : (Fin 6 × G) → K) (ab : G × G) :
    MvPolynomial.aeval x (coordinatePolynomial (K := K) ab) =
      GroupCoordinates.parameterMap (fun i a => x (i, a)) ab := by
  simp [coordinatePolynomial, GroupCoordinates.parameterMap, GroupCoordinates.coordinate]

def affineFiberIdeal (q : G × G → K) : Ideal (MvPolynomial (Fin 6 × G) K) :=
  Ideal.span (Set.range (fun ab => coordinatePolynomial ab - MvPolynomial.C (q ab)))

theorem affineFiberSet_eq_zeroLocus (q : G × G → K) :
    affineFiberSet q = MvPolynomial.zeroLocus K (affineFiberIdeal q) := by
  rw [affineFiberIdeal, MvPolynomial.zeroLocus_span]
  ext x
  constructor
  · intro hx P hP
    obtain ⟨ab, rfl⟩ := hP
    simpa only [map_sub, aeval_coordinatePolynomial, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using congrFun hx ab
  · intro hx
    funext ab
    have h := hx _ ⟨ab, rfl⟩
    simpa only [map_sub, aeval_coordinatePolynomial, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using h

theorem pullback_affineFiberSet (q : G × G → K) :
    pullbackSet (SixFamilyAlgebraic.affineFiberSet addTranslationPerm q) = affineFiberSet q := by
  ext x
  change SixFamilyFibers.parameterMap addTranslationPerm
    (SixFamilyFibers.Parameters.ofCoordinates (polynomialMap forwardPolynomials x)) = q ↔ _
  rw [ofCoordinates_forward, SixFamilyFibers.group_parameterMap]
  rfl

section Composition

variable {I J H : Type*}

theorem polynomialMap_substitution (F : J → MvPolynomial I K) (P : H → MvPolynomial J K)
    (x : I → K) :
    polynomialMap (fun h => MvPolynomial.aeval F (P h)) x =
      polynomialMap P (polynomialMap F x) := by
  funext h
  exact evaluate_substitution F x (P h)

def compose {V : Set (I → K)} {W : Set (J → K)} {U : Set (H → K)}
    (f : PolynomialEquiv V W) (g : PolynomialEquiv W U) : PolynomialEquiv V U where
  forward h := MvPolynomial.aeval f.forward (g.forward h)
  inverse i := MvPolynomial.aeval g.inverse (f.inverse i)
  forward_mem x hx := by
    rw [polynomialMap_substitution]
    exact g.forward_mem _ (f.forward_mem x hx)
  inverse_mem x hx := by
    rw [polynomialMap_substitution]
    exact f.inverse_mem _ (g.inverse_mem x hx)
  left_inverse x hx := by
    rw [polynomialMap_substitution, polynomialMap_substitution,
      g.left_inverse _ (f.forward_mem x hx), f.left_inverse x hx]
  right_inverse x hx := by
    rw [polynomialMap_substitution, polynomialMap_substitution,
      f.right_inverse _ (g.inverse_mem x hx), g.right_inverse x hx]

end Composition

end Sunlet.SixFamilyLiteral

namespace Sunlet.GroupCoordinates

variable {K G : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem translation_loop_mul (x y : G) :
    ((translationLatinSystem (G := G)).loopAt 0).mul x y = x + y := by
  let E : G ≃ G := Equiv.ofBijective
    (fun a => (translationLatinSystem (G := G)).perm a 0)
    ((translationLatinSystem (G := G)).column_bijective 0)
  have hE : E.symm x = x := by
    have h := E.apply_symm_apply x
    simpa [E, translationLatinSystem, addTranslationPerm] using h
  change E.symm x + y = x + y
  rw [hE]

/-- For an abelian group viewed as a loop, the universal abelianization
constructed from the presentation is the original group itself. -/
def translationAbelianGroupEquiv :
    ((translationLatinSystem (G := G)).loopAt 0).AbelianGroup ≃+ G := by
  let L := (translationLatinSystem (G := G)).loopAt 0
  let f : L.AbelianGroup →+ G :=
    L.lift id rfl (fun x y => translation_loop_mul x y)
  have hf (x : G) : f (L.toAbelianGroup x) = x :=
    L.lift_toAbelianGroup id rfl (fun x y => translation_loop_mul x y) x
  exact
    { toFun := f
      invFun := L.toAbelianGroup
      left_inv := fun q => by
        obtain ⟨x, rfl⟩ := L.toAbelianGroup_surjective q
        exact congrArg L.toAbelianGroup (hf x)
      right_inv := hf
      map_add' := f.map_add }

/-- General fibers for the six literal edge families of Section 5.
All components are closed, pairwise disjoint, and exhaust the full affine
fiber.  Their polynomial target has `3 + card G` independent unit pairs
and one free coordinate. -/
theorem six_family_general_fiber (hm : 5 ≤ Fintype.card G) :
    ∃ W : MvPolynomial (G × G) K,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) addTranslationPerm) W).Nonempty ∧
      MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) addTranslationPerm) W)) =
          imageClosure (K := K) (G := G) ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) addTranslationPerm) W,
          ∃ C : Fin (2 * Fintype.card G ^ 2) → Set ((Fin 6 × G) → K),
            (∀ j, ∃ A : Ideal (MvPolynomial (Fin 6 × G) K), C j = MvPolynomial.zeroLocus K A) ∧
            Pairwise (fun i j => Disjoint (C i) (C j)) ∧
            (⋃ j, C j) = SixFamilyLiteral.affineFiberSet q ∧
            ∀ j, Nonempty (AlgebraicSets.PolynomialEquiv (C j)
              (SixFamilyAlgebraic.gaugeSpace (K := K) (ι := G))) := by
  let L := translationLatinSystem (G := G)
  obtain ⟨hc, W, hn, hd, hf⟩ := L.six_family_general_algebraic_fiber (K := K) 0 hm
  refine ⟨W, hn, ?_, ?_⟩
  · rw [imageClosure_eq_fiveFamily]
    exact hd
  · intro q hq
    obtain ⟨hrows, C, hclosed, hdisjoint, hcover, hiso⟩ := hf q hq
    let J := L.DiscreteFiber (K := K) 0
    letI : Fintype J := Fintype.ofFinite J
    have hJ : Fintype.card J = 2 * Fintype.card G ^ 2 := by
      have hcard := Nat.card_congr (translationAbelianGroupEquiv (G := G)).toEquiv
      calc
        Fintype.card J = Nat.card J := Nat.card_eq_fintype_card.symm
        _ = 2 * Nat.card (L.loopAt 0).AbelianGroup ^ 2 := hc
        _ = 2 * Fintype.card G ^ 2 := by rw [hcard, Nat.card_eq_fintype_card]
    let f : J ≃ Fin (2 * Fintype.card G ^ 2) := Fintype.equivFinOfCardEq hJ
    refine ⟨fun j => SixFamilyLiteral.pullbackSet (C (f.symm j)), ?_, ?_, ?_, ?_⟩
    · intro j
      exact SixFamilyLiteral.pullback_isAlgebraic (C (f.symm j)) (hclosed (f.symm j))
    · intro i j hij
      exact SixFamilyLiteral.pullback_disjoint (C (f.symm i)) (C (f.symm j))
        (hdisjoint (fun h => hij (f.symm.injective h)))
    · rw [← SixFamilyLiteral.pullback_affineFiberSet]
      change (⋃ j, C j) = SixFamilyAlgebraic.affineFiberSet addTranslationPerm q at hcover
      rw [← hcover]
      ext x
      simp only [SixFamilyLiteral.pullbackSet, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨f.symm j, hj⟩
      · rintro ⟨p, hp⟩
        refine ⟨f p, ?_⟩
        simpa only [f.symm_apply_apply] using hp
    · intro j
      obtain ⟨h⟩ := hiso (f.symm j)
      exact ⟨SixFamilyLiteral.compose (SixFamilyLiteral.pullbackEquiv (C (f.symm j))) h⟩

end Sunlet.GroupCoordinates
end
end Stage_SixFamilyLiteral

#check "SUNLET_SixFamilyLiteral_READY"

section Stage_PrimeLoopPointAmbiguity



/-!
# Literal parameter ambiguity when the universal abelianization is trivial

The field automorphism statement is supplemented by a statement about every
normalized parameter point above one dense open of the actual model. The
diagonal parameters remain affine in the quantified source. Their values
are forced by the output, and the two component parameter pairs are then
determined up to their literal interchange.
-/

noncomputable section

namespace Sunlet.Normalization

variable {K ι Ω : Type*} [CommRing K] [DecidableEq ι] {e : ι} {o : Ω}

def interchangeParameters (p : Parameters K ι Ω e o) : Parameters K ι Ω e o where
  z := p.z
  k := p.l
  l := p.k
  u := p.v
  v := p.u
  k_base := p.l_base
  l_base := p.k_base

theorem interchangeParameters_parameterMap (π : ι → Equiv.Perm Ω)
    (p : Parameters K ι Ω e o) :
    parameterMap π (interchangeParameters p) = parameterMap π p := by
  funext ab
  by_cases ha : ab.1 = e
  · simp only [parameterMap, coordinate, interchangeParameters, dif_pos ha]
  · simp only [parameterMap, coordinate, interchangeParameters, dif_neg ha, add_comm]

theorem parameters_ext {p q : Parameters K ι Ω e o}
    (hz : p.z = q.z) (hk : p.k = q.k) (hl : p.l = q.l)
    (hu : p.u = q.u) (hv : p.v = q.v) : p = q := by
  cases p
  cases q
  cases hz
  cases hk
  cases hl
  cases hu
  cases hv
  rfl

end Sunlet.Normalization

namespace Sunlet.FiberPoints

variable {K ι Ω : Type*} [Field K] [DecidableEq Ω]
  (L : LoopData Ω) (e : ι ≃ {x : Ω // x ≠ L.identity})
  (π : ι → Equiv.Perm Ω) (hπ : ∀ a, π a = L.left (e a))

include hπ in
theorem parameters_eq_of_point_eq [Subsingleton (L.characterSubgroup (M := Kˣ))]
    (p q : Parameters K ι Ω L.identity) (hp : ∀ a, p.coefficient a ≠ 0)
    (h : q.point L π = p.point L π) : q = p := by
  let E := pointFiberEquiv L e π hπ p hp
  have he : (⟨q, h⟩ : PointFiber L π p) = ⟨p, rfl⟩ :=
    E.injective (Subsingleton.elim _ _)
  exact congrArg Subtype.val he

end Sunlet.FiberPoints

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {K ι Ω : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

theorem normalizedParameters_diagonal_of_map_eq
    (r : Normalization.Parameters K ι Ω L.identity o) (q : ι × Ω → K)
    (hr : Normalization.parameterMap L.perm r = q) :
    r.z = fun b => q (L.identity, b) := by
  funext b
  have h := congrFun hr (L.identity, b)
  simpa [Normalization.parameterMap, Normalization.coordinate] using h

theorem normalizedParameters_nonidentity
    (r : Normalization.Parameters K ι Ω L.identity o)
    (a : L.NonidentityColor) (b : Ω) :
    Normalization.parameterMap L.perm r (a.val, b) =
      r.z (L.nonidentityPerm a b) *
        ((toricPoint L.nonidentityPerm r.u r.k) (a, b) +
          (toricPoint L.nonidentityPerm r.v r.l) (a, b)) := by
  simp [Normalization.parameterMap, Normalization.coordinate, a.property,
    toricPoint, ToricDifferential.coordinate, ToricDifferential.ratio,
    div_eq_mul_inv, Units.val_inv_eq_inv_val, mul_assoc, nonidentityPerm]

theorem normalizedParameters_sum_of_map_eq
    (r : Normalization.Parameters K ι Ω L.identity o) (q : ι × Ω → K)
    (hr : Normalization.parameterMap L.perm r = q)
    (hd : ∀ b, q (L.identity, b) ≠ 0) :
    toricPoint L.nonidentityPerm r.u r.k + toricPoint L.nonidentityPerm r.v r.l =
      L.offDiagonalRatios q := by
  funext ax
  have h := congrFun hr (ax.1.val, ax.2)
  rw [L.normalizedParameters_nonidentity o,
    L.normalizedParameters_diagonal_of_map_eq o r q hr] at h
  change _ = q (ax.1.val, ax.2) / q (L.identity, L.nonidentityPerm ax.1 ax.2)
  apply (eq_div_iff (hd _)).mpr
  simpa only [Pi.add_apply, mul_comm] using h

/-- Trivial universal abelianization leaves precisely the two literal
normalized parameter points, even when the diagonal and coefficient
families of alternative preimages are quantified as affine parameters. -/
theorem generic_parameter_interchange
    (hm : 5 ≤ Fintype.card Ω) (hc : Nat.card (L.loopAt o).AbelianGroup = 1) :
    ∃ W : MvPolynomial (ι × Ω) K,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W).Nonempty ∧
      MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W)) =
          Sunlet.imageClosure L.perm ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.perm) W,
        ∃ p : Normalization.Parameters K ι Ω L.identity o,
          Normalization.parameterMap L.perm p = q ∧
          p ≠ Normalization.interchangeParameters p ∧
          ∀ r : Normalization.Parameters K ι Ω L.identity o,
            Normalization.parameterMap L.perm r = q ↔
              r = p ∨ r = Normalization.interchangeParameters p := by
  have hchar : Nat.card ((L.loopAt o).characterSubgroup (M := Kˣ)) = 1 :=
    ((L.loopAt o).character_card (K := K)).trans hc
  letI : Subsingleton ((L.loopAt o).characterSubgroup (M := Kˣ)) :=
    (Nat.card_eq_one_iff_unique.mp hchar).1
  obtain ⟨P, hP, _, _, hdecomp⟩ := L.generic_unique_torus_decomposition (k := K) o hm
  obtain ⟨W, hW, hchart⟩ := L.exists_model_open_over_secant_open (K := K) o P hP
  refine ⟨W, PolynomialImage.principalOpen_nonempty _ _ hW,
    PolynomialImage.principalOpen_dense _ _ hW, ?_⟩
  intro q hq
  obtain ⟨hd, hz⟩ := hchart q hq
  obtain ⟨U, V, h, g, hb, gb, hU, hV, hs, hne, huniq⟩ :=
    hdecomp (L.offDiagonalRatios q) hz
  let d : Ω → Kˣ := fun b => Units.mk0 (q (L.identity, b)) (hd b)
  let n : NormalizationFibers.Normalized (R := K) L.identity o :=
    ⟨d, h, g, U, V, hb, gb⟩
  let p := n.toParameters
  have hp : Normalization.parameterMap L.perm p = q := by
    rw [← L.coordinatesOfDiagonal_normalized o n]
    change L.coordinatesOfDiagonal d
      (toricPoint L.nonidentityPerm U h + toricPoint L.nonidentityPerm V g) = q
    rw [hs]
    exact L.coordinatesOfDiagonal_ratios q hd
  have hpne : p ≠ Normalization.interchangeParameters p := by
    intro he
    exact hne (congrArg (fun r : Normalization.Parameters K ι Ω L.identity o =>
      toricPoint L.nonidentityPerm r.u r.k) he)
  refine ⟨p, hp, hpne, ?_⟩
  intro r
  constructor
  · intro hr
    let r₁ : FiberPoints.Parameters K L.NonidentityColor Ω o := ⟨r.u, r.k, r.k_base⟩
    let r₂ : FiberPoints.Parameters K L.NonidentityColor Ω o := ⟨r.v, r.l, r.l_base⟩
    let p₁ : FiberPoints.Parameters K L.NonidentityColor Ω o := ⟨U, h, hb⟩
    let p₂ : FiberPoints.Parameters K L.NonidentityColor Ω o := ⟨V, g, gb⟩
    have hx : toricPoint L.nonidentityPerm r.u r.k ∈ toricClosure (k := K) o L.nonidentityPerm :=
      parameterImage_subset_toricClosure o L.nonidentityPerm ⟨r.u, r.k, r.k_base, rfl⟩
    have hy : toricPoint L.nonidentityPerm r.v r.l ∈ toricClosure (k := K) o L.nonidentityPerm :=
      parameterImage_subset_toricClosure o L.nonidentityPerm ⟨r.v, r.l, r.l_base, rfl⟩
    have hz' : r.z = p.z := L.normalizedParameters_diagonal_of_map_eq o r q hr
    have hu := huniq _ hx _ hy (L.normalizedParameters_sum_of_map_eq o r q hr hd)
    rcases hu with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have he₁ : r₁ = p₁ := FiberPoints.parameters_eq_of_point_eq (L.loopAt o)
        (L.loopColorEquiv o).symm L.nonidentityPerm (L.loop_colors_compatible o) p₁ r₁ hU h₁.symm
      have he₂ : r₂ = p₂ := FiberPoints.parameters_eq_of_point_eq (L.loopAt o)
        (L.loopColorEquiv o).symm L.nonidentityPerm (L.loop_colors_compatible o) p₂ r₂ hV h₂.symm
      exact Or.inl (Normalization.parameters_ext hz'
        (congrArg FiberPoints.Parameters.torus he₁)
        (congrArg FiberPoints.Parameters.torus he₂)
        (congrArg FiberPoints.Parameters.coefficient he₁)
        (congrArg FiberPoints.Parameters.coefficient he₂))
    · have he₁ : r₁ = p₂ := FiberPoints.parameters_eq_of_point_eq (L.loopAt o)
        (L.loopColorEquiv o).symm L.nonidentityPerm (L.loop_colors_compatible o) p₂ r₁ hV h₂.symm
      have he₂ : r₂ = p₁ := FiberPoints.parameters_eq_of_point_eq (L.loopAt o)
        (L.loopColorEquiv o).symm L.nonidentityPerm (L.loop_colors_compatible o) p₁ r₂ hU h₁.symm
      exact Or.inr (Normalization.parameters_ext hz'
        (congrArg FiberPoints.Parameters.torus he₁)
        (congrArg FiberPoints.Parameters.torus he₂)
        (congrArg FiberPoints.Parameters.coefficient he₁)
        (congrArg FiberPoints.Parameters.coefficient he₂))
  · rintro (rfl | rfl)
    · exact hp
    · exact (Normalization.interchangeParameters_parameterMap L.perm p).trans hp

end Sunlet.NormalizedLatinSystem

namespace Sunlet.LoopData

variable {K Ω : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Fintype Ω] [DecidableEq Ω] (L : LoopData Ω)

/-- Corollary 5.1 with literal parameter points: over one dense nonempty
open of the original image, all normalized preimages are exactly one
point and its distinct component interchange. -/
theorem paper_corollary_5_1_point_ambiguity (hm : 5 ≤ Fintype.card Ω)
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative) :
    ∃ W : MvPolynomial (Ω × Ω) K,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.left) W).Nonempty ∧
      MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.left) W)) =
          Sunlet.imageClosure L.left ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := K) L.left) W,
        ∃ p : Normalization.Parameters K Ω Ω L.identity L.identity,
          Normalization.parameterMap L.left p = q ∧
          p ≠ Normalization.interchangeParameters p ∧
          ∀ r : Normalization.Parameters K Ω Ω L.identity L.identity,
            Normalization.parameterMap L.left r = q ↔
              r = p ∨ r = Normalization.interchangeParameters p := by
  apply L.asLatin.generic_parameter_interchange (K := K) L.identity hm
  rw [L.loopAt_asLatin, Nat.card_eq_fintype_card]
  exact L.abelianGroup_card_eq_one_of_prime_nonassociative hprime hnonassoc

end Sunlet.LoopData
end
end Stage_PrimeLoopPointAmbiguity

#check "SUNLET_PrimeLoopPointAmbiguity_READY"

section Stage_ModelRationality



/-!
# Rationality after restoring the diagonal coordinates

The field here is generated by the literal normalized coordinates of the
five-family model.  Restoring the diagonal coordinates is a purely
transcendental extension of the off-diagonal secant field, because each
diagonal is independent and invertible in the function field.
-/

noncomputable section

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

/-- Rationality over the original characteristic-zero ground field, with
all independent diagonal coordinates retained.  In particular the
statement applies over ℚ, without assuming that ℚ is algebraically closed. -/
theorem normalizedImage_rational (hm : 5 ≤ Fintype.card Ω) :
    ∃ n : ℕ, 0 < n ∧ Nonempty
      (FractionRing (MvPolynomial (Ω ⊕ (Bool × Fin n)) k) ≃ₐ[k]
        L.NormalizedImageField (k := k) o) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := L.offDiagonal_rational (k := k) o hm
  let q := genericCoordinates (k := k) o L.nonidentityPerm
  let target := fun ax : L.NonidentityColor × Ω => L.nonidentityPerm ax.1 ax.2
  let F := JacobianFinite.generatedField q
  let C := FractionRing (MvPolynomial (Bool × Fin n) k)
  let ec : FractionRing (MvPolynomial Ω C) ≃ₐ[k]
      FractionRing (MvPolynomial Ω F) :=
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.mapAlgEquiv Ω e)
  let er : FractionRing (MvPolynomial Ω F) ≃ₐ[k]
      L.NormalizedImageField (k := k) o :=
    (RationalBaseChange.baseEmbedding (k := k) (J := Ω) q).equivFieldRange.trans
      (IntermediateField.equivOfEq (by
        rw [L.normalizedImageField_eq (k := k) o,
          RationalBaseChange.imageField_eq_range]))
  exact ⟨n, hn, ⟨(IteratedRationalField.combinedEquiv
    (k := k) (I := Bool × Fin n) (J := Ω)).trans (ec.trans er)⟩⟩

include o in
/-- Rationality of the actual image closure of the original five-family
polynomial map.  Its function field is defined from that map's kernel,
and the equivalence above is transported through the proved equality of
the original and normalized equations. -/
theorem model_rational (hm : 5 ≤ Fintype.card Ω) :
    ∃ n : ℕ, 0 < n ∧ Nonempty
      (FractionRing (MvPolynomial (Ω ⊕ (Bool × Fin n)) k) ≃ₐ[k]
        L.ModelFunctionField (k := k)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := L.normalizedImage_rational (k := k) o hm
  exact ⟨n, hn, ⟨e.trans (L.modelFunctionFieldEquivNormalizedImage (k := k) o).symm⟩⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_ModelRationality

#check "SUNLET_ModelRationality_READY"

section Stage_SecantRationality



/-!
# The rational function field of the actual secant closure

The defining ideal is the full kernel of the literal generic sum map.
Its equality with the vanishing ideal of the actual secant closure is
proved before the fraction-field equivalence is used.
-/

noncomputable section

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra
open scoped IntermediateField.algebraAdjoinAdjoin

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

abbrev SecantCoordinateRing :=
  MvPolynomial (L.NonidentityColor × Ω) k ⧸ genericSumIdeal (k := k) o L.nonidentityPerm

instance secantCoordinateRing_isDomain : IsDomain (L.SecantCoordinateRing (k := k) o) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    (RingHom.ker_isPrime (MvPolynomial.aeval (R := k)
      (genericCoordinates (k := k) o L.nonidentityPerm)))

theorem secant_definingIdeal :
    genericSumIdeal (k := k) o L.nonidentityPerm =
      MvPolynomial.vanishingIdeal k (secantClosure (k := k) o L.nonidentityPerm) := by
  rw [genericSumIdeal_eq_vanishingIdeal, secantClosure,
    PolynomialClosureProduct.closure, PolynomialImage.vanishingIdeal_closure]

abbrev SecantFunctionField := FractionRing (L.SecantCoordinateRing (k := k) o)

def secantCoordinateRingEquivGeneratedAlgebra :
    L.SecantCoordinateRing (k := k) o ≃ₐ[k]
      Algebra.adjoin k (Set.range (genericCoordinates (k := k) o L.nonidentityPerm)) :=
  (Ideal.quotientKerEquivRange (MvPolynomial.aeval (R := k)
    (genericCoordinates (k := k) o L.nonidentityPerm))).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_range_eq_range_aeval k _).symm)

def secantFunctionFieldEquivGeneratedField :
    L.SecantFunctionField (k := k) o ≃ₐ[k]
      JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm) :=
  IsFractionRing.algEquivOfAlgEquiv (L.secantCoordinateRingEquivGeneratedAlgebra (k := k) o)

/-- Rationality of the secant variety over the ground field itself,
including k=ℚ, with the full actual defining ideal retained. -/
theorem secant_rational (hm : 5 ≤ Fintype.card Ω) :
    ∃ n : ℕ, 0 < n ∧ Nonempty
      (FractionRing (MvPolynomial (Bool × Fin n) k) ≃ₐ[k]
        L.SecantFunctionField (k := k) o) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := L.offDiagonal_rational (k := k) o hm
  exact ⟨n, hn, ⟨e.trans (L.secantFunctionFieldEquivGeneratedField (k := k) o).symm⟩⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_SecantRationality

#check "SUNLET_SecantRationality_READY"

#check @Sunlet.NormalizedLatinSystem.paper_theorem_4_2_algebraic_fibers
#print axioms Sunlet.NormalizedLatinSystem.paper_theorem_4_2_algebraic_fibers
#check @Sunlet.GroupCoordinates.six_family_general_fiber
#print axioms Sunlet.GroupCoordinates.six_family_general_fiber
#check @Sunlet.LoopData.paper_corollary_5_1_point_ambiguity
#print axioms Sunlet.LoopData.paper_corollary_5_1_point_ambiguity
#check @Sunlet.NormalizedLatinSystem.model_rational
#print axioms Sunlet.NormalizedLatinSystem.model_rational
#check @Sunlet.NormalizedLatinSystem.secant_rational
#print axioms Sunlet.NormalizedLatinSystem.secant_rational
