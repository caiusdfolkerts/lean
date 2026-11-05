module

public import sunlet.orbit_models

/-! Initial monomials selected by a coarse partition, with the actual
independent variables indexed by the fine partition. The final dimension
criterion assumes the explicitly stated canonical-kernel lemma; applications
must prove that lemma rather than treating it as an axiom. -/

@[expose] public section
noncomputable section
open scoped BigOperators MonomialOrder
open MvPolynomial

namespace Sunlet.CoarseSelection

variable {K G C D : Type*} [Field K] [AddCommGroup G]
  [Fintype G] [Fintype C] [DecidableEq C] [Fintype D] [LinearOrder D]

def selectsU (q : G → C) (p : C → D) (σ : Set D) (b c : G) : Prop :=
  ClassSelection.selectsU (p ∘ q) σ b c

instance (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)] (b c : G) :
    Decidable (selectsU q p σ b c) := by unfold selectsU; infer_instance

def uExponent (q : G → C) (bc : G × G) : ParamVar C C →₀ ℕ :=
  (Finsupp.single (.s (q bc.1)) 1 + Finsupp.single (.t (q bc.2)) 1) +
    (Finsupp.single (.u (q (bc.2 - bc.1))) 1 + Finsupp.single (.h (q bc.2)) 1)

def vExponent (q : G → C) (bc : G × G) : ParamVar C C →₀ ℕ :=
  (Finsupp.single (.s (q bc.1)) 1 + Finsupp.single (.t (q bc.2)) 1) +
    (Finsupp.single (.v (q (bc.2 - bc.1))) 1 + Finsupp.single (.h (q bc.1)) 1)

def selectedExponent (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (bc : G × G) : ParamVar C C →₀ ℕ :=
  if selectsU q p σ bc.1 bc.2 then uExponent q bc else vExponent q bc

def parentVariable (p : C → D) : ParamVar C C → ParamVar D D
  | .s i => .s (p i)
  | .t i => .t (p i)
  | .h i => .h (p i)
  | .u i => .u (p i)
  | .v i => .v (p i)

def reverseWeight (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (i : ParamVar C C) : ℕ := ClassSelection.reverseWeight σ (parentVariable p i)

def liftedVariable (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (i : ParamVar C C) : WithBot (ParamVar C C) →₀ ℕ :=
  Finsupp.single (i : WithBot (ParamVar C C)) 1 + Finsupp.single ⊥ (reverseWeight p σ i)

def liftedU (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (bc : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  (liftedVariable p σ (.s (q bc.1)) + liftedVariable p σ (.t (q bc.2))) +
    (liftedVariable p σ (.u (q (bc.2 - bc.1))) + liftedVariable p σ (.h (q bc.2)))

def liftedV (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (bc : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  (liftedVariable p σ (.s (q bc.1)) + liftedVariable p σ (.t (q bc.2))) +
    (liftedVariable p σ (.v (q (bc.2 - bc.1))) + liftedVariable p σ (.h (q bc.1)))

def selectedLifted (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (bc : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  if selectsU q p σ bc.1 bc.2 then liftedU q p σ bc else liftedV q p σ bc

def weightHom (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)] :
    MvPolynomial (ParamVar C C) K →ₐ[K] MvPolynomial (WithBot (ParamVar C C)) K :=
  aeval fun i => monomial (liftedVariable p σ i) 1

theorem weightHom_coordinate (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (bc : G × G) :
    weightHom (K := K) p σ (Identified.coordinatePolynomial q (bc.2 - bc.1, bc.1)) =
      monomial (liftedU q p σ bc) 1 + monomial (liftedV q p σ bc) 1 := by
  simp [weightHom, Identified.coordinatePolynomial, liftedU, liftedV, mul_add, monomial_mul]

theorem selectedLifted_coe (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (bc : G × G) (i : ParamVar C C) :
    selectedLifted q p σ bc (i : WithBot (ParamVar C C)) = selectedExponent q p σ bc i := by
  simp only [selectedLifted, selectedExponent]
  split_ifs <;> simp [liftedU, liftedV, liftedVariable, uExponent, vExponent, Finsupp.single_apply]

theorem liftedU_bot (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (bc : G × G) :
    liftedU q p σ bc ⊥ = ClassSelection.liftedU (p ∘ q) σ bc ⊥ := by
  simp [liftedU, liftedVariable, reverseWeight, parentVariable,
    ClassSelection.liftedU, ClassSelection.liftedVariable]

theorem liftedV_bot (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (bc : G × G) :
    liftedV q p σ bc ⊥ = ClassSelection.liftedV (p ∘ q) σ bc ⊥ := by
  simp [liftedV, liftedVariable, reverseWeight, parentVariable,
    ClassSelection.liftedV, ClassSelection.liftedVariable]

/-- The weight comparison uses only the coarse order; every non-bottom
exponent still records its actual fine variable. -/
theorem strict_selected_weight (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (bc : G × G) :
    if selectsU q p σ bc.1 bc.2 then liftedV q p σ bc ⊥ < liftedU q p σ bc ⊥
    else liftedU q p σ bc ⊥ < liftedV q p σ bc ⊥ := by
  simpa only [selectsU, liftedU_bot, liftedV_bot] using
    ClassSelection.strict_selected_weight (p ∘ q) σ bc

section MonomialOrder

variable [LinearOrder (ParamVar C C)]

theorem weighted_leading (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (bc : G × G) :
    MonomialOrder.lex.degree
        (weightHom (K := K) p σ (Identified.coordinatePolynomial q (bc.2 - bc.1, bc.1))) =
        selectedLifted q p σ bc ∧
      MonomialOrder.lex.Monic
        (weightHom (K := K) p σ (Identified.coordinatePolynomial q (bc.2 - bc.1, bc.1))) := by
  classical
  let m : MonomialOrder (WithBot (ParamVar C C)) := MonomialOrder.lex
  have hw := strict_selected_weight q p σ bc
  rw [weightHom_coordinate, selectedLifted]
  by_cases hs : selectsU q p σ bc.1 bc.2
  · simp only [if_pos hs] at hw ⊢
    have hlt : m.degree (monomial (liftedV q p σ bc) (1 : K)) ≺[m]
        m.degree (monomial (liftedU q p σ bc) (1 : K)) := by
      simpa [m.degree_monomial] using (WeightedInitial.lex_lt_of_bot hw)
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩
  · simp only [if_neg hs] at hw ⊢
    have hlt : m.degree (monomial (liftedU q p σ bc) (1 : K)) ≺[m]
        m.degree (monomial (liftedV q p σ bc) (1 : K)) := by
      simpa [m.degree_monomial] using (WeightedInitial.lex_lt_of_bot hw)
    rw [add_comm]
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩

end MonomialOrder

theorem coordinate_subfamily_algebraicIndependent
    {I : Type*} [Fintype I] (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (r : I → G × G)
    (hr : LinearIndependent ℚ (fun j i => (selectedExponent q p σ (r j) i : ℚ))) :
    AlgebraicIndependent K (fun j =>
      Identified.coordinatePolynomial (K := K) q ((r j).2 - (r j).1, (r j).1)) := by
  classical
  letI : LinearOrder (ParamVar C C) := LinearOrder.lift'
    (Fintype.equivFin (ParamVar C C)) (Fintype.equivFin (ParamVar C C)).injective
  let m : MonomialOrder (WithBot (ParamVar C C)) := MonomialOrder.lex
  let f : I → MvPolynomial (ParamVar C C) K := fun j =>
    Identified.coordinatePolynomial q ((r j).2 - (r j).1, (r j).1)
  let φ := weightHom (K := K) p σ
  have hdegree (j : I) : m.degree (φ (f j)) = selectedLifted q p σ (r j) :=
    (weighted_leading q p σ (r j)).1
  have hn (j : I) : φ (f j) ≠ 0 := (weighted_leading q p σ (r j)).2.ne_zero
  have hlin : LinearIndependent ℚ (fun j i => (m.degree (φ (f j)) i : ℚ)) := by
    apply LinearIndependent.of_comp (WeightedInitial.forgetWeight (ι := C) (Ω := C))
    convert hr using 1
    funext j i
    simp only [Function.comp_apply, WeightedInitial.forgetWeight, LinearMap.coe_mk,
      AddHom.coe_mk, hdegree, selectedLifted_coe]
  exact AlgebraicIndependent.of_comp φ
    (InitialIndependence.algebraicIndependent_of_rational_leading_exponents m
      (fun j => φ (f j)) hn hlin)

def Equation (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (w : ParamVar C C → ℚ) (b c : G) : Prop :=
  w (.s (q b)) + w (.t (q c)) +
    (if selectsU q p σ b c then w (.u (q (c - b))) + w (.h (q c))
    else w (.v (q (c - b))) + w (.h (q b))) = 0

def IsRelation (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (w : ParamVar C C → ℚ) : Prop := ∀ b c, Equation q p σ w b c

def relationMap (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)] :
    (ParamVar C C → ℚ) →ₗ[ℚ] (G × G → ℚ) where
  toFun w bc := w (.s (q bc.1)) + w (.t (q bc.2)) +
    if selectsU q p σ bc.1 bc.2 then w (.u (q (bc.2 - bc.1))) + w (.h (q bc.2))
    else w (.v (q (bc.2 - bc.1))) + w (.h (q bc.1))
  map_add' w z := by funext bc; dsimp; split_ifs <;> ring
  map_smul' r w := by funext bc; dsimp; split_ifs <;> ring

theorem mem_ker_iff (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (w : ParamVar C C → ℚ) :
    w ∈ (relationMap q p σ).ker ↔ IsRelation q p σ w := by
  simp only [LinearMap.mem_ker, funext_iff, Prod.forall, relationMap,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, IsRelation, Equation]

theorem canonical_isRelation (q : G → C) (p : C → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (z : C) (hq0 : ∀ a, q a = z ↔ a = 0)
    (hσ0 : p z ∉ σ) (s k v u : ℚ) :
    IsRelation q p σ (SelectedRelations.canonical z s k v u) := by
  intro b c
  unfold Equation
  by_cases hsel : selectsU q p σ b c
  · have ha : q (c - b) ≠ z := by
      intro he
      have hcb := sub_eq_zero.mp ((hq0 _).mp he)
      subst c
      simpa [selectsU, ClassSelection.selectsU, (hq0 0).mpr rfl, hσ0] using hsel
    simp only [if_pos hsel, SelectedRelations.canonical, if_neg ha]
    ring
  · simp only [if_neg hsel, SelectedRelations.canonical]
    ring

def canonicalKer (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (z : C) (hq0 : ∀ a, q a = z ↔ a = 0) (hσ0 : p z ∉ σ) :
    (Fin 4 → ℚ) →ₗ[ℚ] (relationMap q p σ).ker :=
  (ExponentRank.canonicalLinear z).codRestrict _ fun t =>
    (mem_ker_iff q p σ _).mpr (canonical_isRelation q p σ z hq0 hσ0 (t 0) (t 1) (t 2) (t 3))

/-- The exact fine-class dimension from an actual coarse-selected exponent
kernel. The canonical-kernel hypothesis is an exposed intermediate obligation. -/
theorem imageClosure_dimension_eq [Infinite K]
    (q : G → C) (p : C → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (hqsurj : Function.Surjective q) (z : C) (hq0 : ∀ a, q a = z ↔ a = 0)
    (hσ0 : p z ∉ σ)
    (hcanonical : ∀ w : ParamVar C C → ℚ, IsRelation q p σ w →
      w = SelectedRelations.canonical z (w (.s z)) (w (.s z) + w (.h z))
        (w (.v z)) (w (.u z))) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) q))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  classical
  have hinj : Function.Injective (canonicalKer q p σ z hq0 hσ0) := by
    intro a b h
    apply ExponentRank.canonical_injective z z
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective (canonicalKer q p σ z hq0 hσ0) := by
    intro w
    refine ⟨ExponentRank.decodeLinear z z w, ?_⟩
    apply Subtype.ext
    exact (hcanonical w ((mem_ker_iff q p σ w).mp w.property)).symm
  have hk : Module.finrank ℚ (relationMap q p σ).ker = 4 := by
    let e := LinearEquiv.ofBijective (canonicalKer q p σ z hq0 hσ0) ⟨hinj, hsurj⟩
    simpa using e.finrank_eq.symm
  let M : Matrix (G × G) (ParamVar C C) ℚ := fun bc i => (selectedExponent q p σ bc i : ℚ)
  have hM : M.mulVecLin = relationMap q p σ := by
    apply LinearMap.ext
    intro w
    funext bc
    change (∑ i, (selectedExponent q p σ bc i : ℚ) * w i) = _
    simp only [selectedExponent]
    split_ifs <;> simp [uExponent, vExponent, relationMap, *, Finsupp.add_apply,
      Nat.cast_add, add_mul, Finset.sum_add_distrib, Finsupp.single_apply, add_assoc]
  have hplus : M.rank + 4 = 5 * Fintype.card C := by
    change Module.finrank ℚ M.mulVecLin.range + 4 = _
    rw [hM]
    have h := (relationMap q p σ).finrank_range_add_finrank_ker
    rw [hk] at h
    simp only [Module.finrank_pi, Module.finrank_self, mul_one, ExponentRank.card_paramVar] at h
    omega
  apply le_antisymm
  · apply Identified.imageClosure_dimension_le
    intro a
    simpa only [(hq0 0).mpr rfl] using hq0 a
  · rw [PolynomialImage.vanishingIdeal_imageClosure]
    obtain ⟨I, r, hrinj, hspan, hr⟩ := exists_linearIndependent' ℚ M.row
    letI : Fintype I := Fintype.ofInjective r hrinj
    have hcard : Fintype.card I = M.rank := by
      rw [M.rank_eq_finrank_span_row, ← hspan]
      exact (finrank_span_eq_card hr).symm
    have halg := coordinate_subfamily_algebraicIndependent (K := K) q p σ r hr
    let A := PolynomialImage.imageAlgebra (Identified.coordinatePolynomial (K := K) q)
    let f : I → A := fun j =>
      ⟨Identified.coordinatePolynomial q ((r j).2 - (r j).1, (r j).1), by
        refine ⟨MvPolynomial.X ((r j).2 - (r j).1, (r j).1), ?_⟩
        simp [PolynomialImage.comorphism]⟩
    have hf : AlgebraicIndependent K f := AlgebraicIndependent.of_comp A.val halg
    letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
      (PolynomialImage.comorphism (Identified.coordinatePolynomial (K := K) q)).rangeRestrict
      (PolynomialImage.comorphism (Identified.coordinatePolynomial (K := K) q)).rangeRestrict_surjective
    have hd := DimensionAlgebra.card_le_ringKrullDim_of_algebraicIndependent K A f hf
    have hsize : Fintype.card I = 5 * Fintype.card C - 4 := by omega
    rw [ringKrullDim_eq_of_ringEquiv
      (PolynomialImage.coordinateRingEquivImage (Identified.coordinatePolynomial (K := K) q)).toRingEquiv]
    simpa only [hsize] using hd

end Sunlet.CoarseSelection
