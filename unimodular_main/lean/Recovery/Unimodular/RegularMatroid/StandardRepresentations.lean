module

public import Recovery.Unimodular.RegularMatroid.RepresentationCore
public import Recovery.Unimodular.PriorExtensions.SignedSumsMatroid
public import Recovery.Unimodular.RegularMatroid.ModularTUCriterion
public import Mathlib.LinearAlgebra.Matrix.Block

set_option maxHeartbeats 0


@[expose] public section

/-! # A common matroid basis and the binary/ternary criterion

The representations below are ordinary labelled vector matroids. In particular,
zero vectors, repeated vectors, and the empty ground set are retained. We first
normalize two representations at the same ordinary matroid basis. Completing
each square minor with the complementary identity columns shows that its zero
status depends only on the matroid. The centred lift of the ternary matrix is
therefore totally unimodular by the unit-pivot criterion.

The field-independence conclusion refers to every subset of the original
ground set; loops and parallel labels remain distinct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open Set Function Submodule
open scoped BigOperators Matroid

namespace Unimodular.RegularRepresentation

open RepresentationBridge
attribute [local instance] Classical.propDecidable

/-- Coordinates in an actual matroid basis give literal identity columns and
preserve every independent subset of labels. The ambient vector space need not
already be the span of the represented vectors. -/
theorem exists_standard_representation {K E V : Type*} [Field K] [Fintype E]
    [AddCommGroup V] [Module K V] (v : E → V) (B : Set E)
    (hB : (VectorMatroid.ofFamily (K := K) v).IsBase B) :
    ∃ A : Matrix B E K,
      VectorMatroid.ofFamily (K := K) (fun j i => A i j) =
        VectorMatroid.ofFamily (K := K) v ∧
      ∀ i j : B, A i j.val = if i = j then 1 else 0 := by
  classical
  obtain ⟨hli, hspan⟩ := (ofFamily_isBase_iff K v B).1 hB
  let S := span K (range (fun b : B => v b.val))
  let b : Module.Basis B K S := Module.Basis.span hli
  let vS : E → S := fun e => ⟨v e, by
    simpa only [S, Set.image_eq_range] using hspan e⟩
  let A : Matrix B E K := fun i j => b.equivFun (vS j) i
  refine ⟨A, ?_, ?_⟩
  · apply (VectorMatroid.ofFamily_eq_iff _ _).2
    intro I
    have h₁ := S.subtype.linearIndepOn_iff_of_injOn S.injective_subtype.injOn
      (v := vS) (s := I)
    have h₂ := b.equivFun.toLinearMap.linearIndepOn_iff_of_injOn
      b.equivFun.injective.injOn (v := vS) (s := I)
    exact h₂.trans h₁.symm
  · intro i j
    have hv : vS j.val = b j := by
      apply Subtype.ext
      exact (Module.Basis.coe_span_apply hli j).symm
    change b.equivFun (vS j.val) i = _
    rw [hv]
    simpa only [eq_comm] using b.equivFun_self j i

/-- Reindexing two representations of the same labelled matroid preserves
linear independence even for a noninjective selector. In that case both
families have a repeated label and are dependent. -/
theorem linearIndependent_comp_iff {K L E J V W : Type*}
    [Field K] [Field L] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module L W] (v : E → V) (w : E → W)
    (hM : VectorMatroid.ofFamily (K := K) v =
      VectorMatroid.ofFamily (K := L) w) (q : J → E) :
    LinearIndependent K (v ∘ q) ↔ LinearIndependent L (w ∘ q) := by
  by_cases hq : Injective q
  · rw [← linearIndepOn_range_iff hq v, ← linearIndepOn_range_iff hq w,
      ← VectorMatroid.ofFamily_indep, hM, VectorMatroid.ofFamily_indep]
  · have hv : ¬ LinearIndependent K (v ∘ q) := by
      intro h
      apply hq
      intro i j hij
      exact h.injective (congrArg v hij)
    have hw : ¬ LinearIndependent L (w ∘ q) := by
      intro h
      apply hq
      intro i j hij
      exact h.injective (congrArg w hij)
    exact iff_of_false hv hw

/-- The same selected labels complete the minor over every coefficient field.
This definition depends only on the row selector and the chosen basis labels. -/
def minorCompletion {I E : Type*} {k : ℕ} (b : I → E)
    (f : Fin k → I) (hf : Injective f) (g : Fin k → E) : I → E :=
  let C := {i : I // i ∉ Set.range f}
  let e : Fin k ⊕ C ≃ I :=
    ((Equiv.ofInjective f hf).sumCongr (Equiv.refl C)).trans
      (Equiv.sumCompl (fun i : I => i ∈ Set.range f))
  Sum.elim g (fun i : C => b i.val) ∘ e.symm

/-- A selected minor is exactly the determinant of its completion by identity
columns. The simultaneous row and column reindexing introduces no sign. -/
theorem det_minorCompletion {K I E : Type*} [CommRing K]
    [Fintype I] [hI : DecidableEq I] (A : Matrix I E K) (b : I → E)
    (hstd : ∀ i j, A i (b j) = if i = j then 1 else 0)
    (k : ℕ) (f : Fin k → I) (hf : Injective f) (g : Fin k → E) :
    (A.submatrix id (minorCompletion b f hf g)).det = (A.submatrix f g).det := by
  classical
  cases Subsingleton.elim hI (Classical.decEq I)
  let C := {i : I // i ∉ Set.range f}
  let e : Fin k ⊕ C ≃ I :=
    ((Equiv.ofInjective f hf).sumCongr (Equiv.refl C)).trans
      (Equiv.sumCompl (fun i : I => i ∈ Set.range f))
  have heL (i : Fin k) : e (Sum.inl i) = f i := rfl
  have heR (i : C) : e (Sum.inr i) = i.val := rfl
  have heLinv (i : Fin k) : e.symm (f i) = Sum.inl i := by
    rw [← heL i, Equiv.symm_apply_apply]
  have heRinv (i : C) : e.symm i.val = Sum.inr i := by
    rw [← heR i, Equiv.symm_apply_apply]
  let h : Fin k ⊕ C → E := Sum.elim g (fun i => b i.val)
  let B : Matrix I I K := A.submatrix id (h ∘ e.symm)
  let D : Matrix C (Fin k) K := fun i j => A i.val (g j)
  have hblock : B.submatrix e e =
      Matrix.fromBlocks (A.submatrix f g) 0 D (1 : Matrix C C K) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j => simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heL]
        | inr j =>
            have hij : f i ≠ j.val := by
              intro he
              exact j.property ⟨i, he⟩
            simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heL, hstd, hij]
    | inr i =>
        cases j with
        | inl j => simp [B, h, D, Matrix.submatrix_apply, heLinv, heRinv, heR]
        | inr j =>
            by_cases hij : i = j
            · subst j
              simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heR, hstd,
                Matrix.one_apply]
            · have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
              simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heR, hstd,
                Matrix.one_apply, hij, hval]
  have hdet : B.det = (A.submatrix f g).det := by
    rw [← Matrix.det_submatrix_equiv_self e B, hblock,
      Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  simpa only [B, h, e, C, minorCompletion] using hdet

/-- For two normalized representations of one matroid, every square minor
has the same zero status. Selectors with repeated rows are included. -/
theorem normalized_minor_zero_iff {K L I E : Type*} [Field K] [Field L]
    [Fintype I] [DecidableEq I] (A : Matrix I E K) (C : Matrix I E L)
    (b : I → E) (hA : ∀ i j, A i (b j) = if i = j then 1 else 0)
    (hC : ∀ i j, C i (b j) = if i = j then 1 else 0)
    (hM : VectorMatroid.ofFamily (K := K) (fun j i => A i j) =
      VectorMatroid.ofFamily (K := L) (fun j i => C i j))
    (k : ℕ) (f : Fin k → I) (g : Fin k → E) :
    (A.submatrix f g).det = 0 ↔ (C.submatrix f g).det = 0 := by
  classical
  by_cases hf : Injective f
  · let q := minorCompletion b f hf g
    have hli := linearIndependent_comp_iff
      (fun j i => A i j) (fun j i => C i j) hM q
    change LinearIndependent K (A.submatrix id q).col ↔
      LinearIndependent L (C.submatrix id q).col at hli
    rw [Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, Matrix.linearIndependent_col_iff_isUnit,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hli
    rw [det_minorCompletion A b hA k f hf g,
      det_minorCompletion C b hC k f hf g] at hli
    simpa only [not_not] using not_congr hli
  · simp only [Function.Injective] at hf
    push_neg at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    have hAz : (A.submatrix f g).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext x; simp [Matrix.submatrix_apply, hij])
    have hCz : (C.submatrix f g).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext x; simp [Matrix.submatrix_apply, hij])
    exact iff_of_true hAz hCz

/-- The canonical representatives 0, 1, -1 of the ternary field. -/
def ternaryLift (x : ZMod 3) : ℤ :=
  letI : DecidableEq (ZMod 3) := ZMod.decidableEq 3
  if x = 0 then 0 else if x = 1 then 1 else -1

theorem ternaryLift_small (x : ZMod 3) :
    ternaryLift x = 0 ∨ ternaryLift x = 1 ∨ ternaryLift x = -1 := by
  unfold ternaryLift
  split_ifs <;> simp

@[simp] theorem ternaryLift_cast_three (x : ZMod 3) :
    (ternaryLift x : ZMod 3) = x := by
  fin_cases x <;> rfl

theorem ternaryLift_cast_two (x : ZMod 2) (y : ZMod 3)
    (h : x = 0 ↔ y = 0) : (ternaryLift y : ZMod 2) = x := by
  by_cases hy : y = 0
  · subst y
    have hx : x = 0 := h.mpr rfl
    subst x
    rfl
  · have hx : x ≠ 0 := fun hx => hy (h.mp hx)
    have hx1 : x = 1 := by
      fin_cases x
      · exact (hx rfl).elim
      · rfl
    subst x
    fin_cases y
    · exact (hy rfl).elim
    · rfl
    · rfl

/-- Simultaneous binary and ternary representability produces a totally
unimodular integer matrix representing exactly the original labelled matroid
over every field. This statement has no rank or ground-set size bound. -/
theorem exists_tu_of_binary_ternary {E : Type*} [Fintype E] (M : Matroid E)
    (h₂ : HasFiniteRepresentation (ZMod 2) M)
    (h₃ : HasFiniteRepresentation (ZMod 3) M) :
    ∃ (B : Set E) (A : Matrix B E ℤ), A.IsTotallyUnimodular ∧
      M = VectorMatroid.ofFamily (K := ℚ) (fun j i => (A i j : ℚ)) := by
  classical
  obtain ⟨n₂, v₂, hv₂⟩ := h₂
  obtain ⟨n₃, v₃, hv₃⟩ := h₃
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨A₂, hA₂, hstd₂⟩ := exists_standard_representation v₂ B (hv₂ ▸ hB)
  obtain ⟨A₃, hA₃, hstd₃⟩ := exists_standard_representation v₃ B (hv₃ ▸ hB)
  letI : Fintype B := Fintype.ofFinite B
  have hsame : VectorMatroid.ofFamily (K := ZMod 2) (fun j i => A₂ i j) =
      VectorMatroid.ofFamily (K := ZMod 3) (fun j i => A₃ i j) :=
    hA₂.trans (hv₂.symm.trans (hv₃.trans hA₃.symm))
  have hmin := normalized_minor_zero_iff A₂ A₃ Subtype.val hstd₂ hstd₃ hsame
  let A : Matrix B E ℤ := fun i j => ternaryLift (A₃ i j)
  have hcast₂ : (fun i j => (A i j : ZMod 2)) = A₂ := by
    ext i j
    apply ternaryLift_cast_two
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using
      hmin 1 (fun _ => i) (fun _ => j)
  have hcast₃ : (fun i j => (A i j : ZMod 3)) = A₃ := by
    ext i j
    exact ternaryLift_cast_three _
  have hmod : ModularTU.ModularAgreement A := by
    intro k f g
    have h₂m : (A.submatrix f g).map (fun z => (z : ZMod 2)) = A₂.submatrix f g := by
      ext i j
      exact congrFun (congrFun hcast₂ (f i)) (g j)
    have h₃m : (A.submatrix f g).map (fun z => (z : ZMod 3)) = A₃.submatrix f g := by
      ext i j
      exact congrFun (congrFun hcast₃ (f i)) (g j)
    rw [h₂m, h₃m]
    exact hmin k f g
  have htu : A.IsTotallyUnimodular :=
    ModularTU.isTotallyUnimodular_of_modularAgreement A
      (fun i j => ternaryLift_small _) hmod
  refine ⟨B, A, htu, ?_⟩
  have hfield := SignedSums.tu_matroid_field_invariant
    (K := ℚ) (F := ZMod 3) A htu
  have hcols : (fun j i => (A i j : ZMod 3)) = (fun j i => A₃ i j) := by
    ext j i
    exact congrFun (congrFun hcast₃ i) j
  rw [hcols] at hfield
  exact hv₃.trans (hA₃.symm.trans hfield.symm)

/-- The same integer matrix works over any field, not just over the rational
field used to state the existence theorem. -/
theorem tu_representation_all_fields {K E I : Type*} [Field K]
    [Fintype E] [Fintype I] (M : Matroid E) (A : Matrix I E ℤ)
    (htu : A.IsTotallyUnimodular)
    (hM : M = VectorMatroid.ofFamily (K := ℚ) (fun j i => (A i j : ℚ))) :
    M = VectorMatroid.ofFamily (K := K) (fun j i => (A i j : K)) :=
  hM.trans (SignedSums.tu_matroid_field_invariant A htu)

/-- Finite representability over the two prime fields is equivalent to
representability by one totally unimodular integer matrix. -/
theorem binary_ternary_iff_tu {E : Type*} [Fintype E] (M : Matroid E) :
    (HasFiniteRepresentation (ZMod 2) M ∧ HasFiniteRepresentation (ZMod 3) M) ↔
      ∃ (B : Set E) (A : Matrix B E ℤ), A.IsTotallyUnimodular ∧
        M = VectorMatroid.ofFamily (K := ℚ) (fun j i => (A i j : ℚ)) := by
  classical
  constructor
  · rintro ⟨h₂, h₃⟩
    exact exists_tu_of_binary_ternary M h₂ h₃
  · rintro ⟨B, A, htu, hM⟩
    letI : Fintype B := Fintype.ofFinite B
    constructor
    · rw [tu_representation_all_fields (K := ZMod 2) M A htu hM]
      exact hasFiniteRepresentation_ofFamily _
    · rw [tu_representation_all_fields (K := ZMod 3) M A htu hM]
      exact hasFiniteRepresentation_ofFamily _

/-- Representability over every field follows from the two prime fields.
The field in this theorem is universe-polymorphic. -/
theorem representable_over_every_field {E : Type*} [Fintype E] (M : Matroid E)
    (h₂ : HasFiniteRepresentation (ZMod 2) M)
    (h₃ : HasFiniteRepresentation (ZMod 3) M) (K : Type*) [Field K] :
    HasFiniteRepresentation K M := by
  classical
  obtain ⟨B, A, htu, hM⟩ := exists_tu_of_binary_ternary M h₂ h₃
  letI : Fintype B := Fintype.ofFinite B
  rw [tu_representation_all_fields (K := K) M A htu hM]
  exact hasFiniteRepresentation_ofFamily _

/-- The usual all-fields definition of regularity. The ground-set
normalization does not delete loops or identify parallel elements. -/
def RegularOnGround {E : Type*} (M : Matroid E) : Prop :=
  ∀ (K : Type) [Field K], RepresentableOnGround K M

/-- The binary/ternary criterion is an equivalence with the all-fields
definition, rather than a substitute definition of regularity. -/
theorem regularOnGround_iff_binary_ternary {E : Type*} (M : Matroid E) [M.Finite] :
    RegularOnGround M ↔
      RepresentableOnGround (ZMod 2) M ∧ RepresentableOnGround (ZMod 3) M := by
  classical
  letI : Fintype M.E := M.ground_finite.fintype
  constructor
  · intro h
    exact ⟨h (ZMod 2), h (ZMod 3)⟩
  · rintro ⟨h₂, h₃⟩ K _
    exact representable_over_every_field (M.restrictSubtype M.E) h₂ h₃ K

/-- Regularity gives representability also for fields in arbitrary
universes. Thus the small-field quantifier in `RegularOnGround` imposes no
mathematical restriction on the field to which the result is applied. -/
theorem RegularOnGround.representable {E : Type*} {M : Matroid E} [M.Finite]
    (h : RegularOnGround M) (K : Type*) [Field K] : RepresentableOnGround K M := by
  letI : Fintype M.E := M.ground_finite.fintype
  exact representable_over_every_field (M.restrictSubtype M.E)
    (h (ZMod 2)) (h (ZMod 3)) K

end Unimodular.RegularRepresentation

end
end

#print axioms Unimodular.RegularRepresentation.exists_tu_of_binary_ternary
#print axioms Unimodular.RegularRepresentation.binary_ternary_iff_tu
#print axioms Unimodular.RegularRepresentation.regularOnGround_iff_binary_ternary
#print axioms Unimodular.RegularRepresentation.RegularOnGround.representable
#check Unimodular.RegularRepresentation.regularOnGround_iff_binary_ternary
