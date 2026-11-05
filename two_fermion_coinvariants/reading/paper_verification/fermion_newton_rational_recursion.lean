module

public import PaperVerification.FermionNewtonContraction
public import Mathlib.Data.Finset.Image

/-!
# Exact rational-column identities under deletion of the first node

These identities retain the actual residue correction in equation (7).
Adding a positive first sign multiplies each surviving row by its linear
factor; adding a negative first sign divides each surviving row by that
factor and supplies the exact new residue row. They hold algebraically in
every field, with all finite index sets left arbitrary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators

variable {L ι κ : Type*} [Field L] [DecidableEq ι] [DecidableEq κ]

theorem nodal_map_embedding (e : ι ↪ κ) (s : Finset ι) (x : κ → L) :
    Lagrange.nodal (s.map e) x = Lagrange.nodal s (x ∘ e) := by
  simp only [Lagrange.nodal, Finset.prod_map, Function.comp_apply]

theorem nodalWeight_map_embedding (e : ι ↪ κ) (s : Finset ι) (x : κ → L) (i : ι) :
    Lagrange.nodalWeight (s.map e) x (e i) = Lagrange.nodalWeight s (x ∘ e) i := by
  simp only [Lagrange.nodalWeight, ← Finset.map_erase, Finset.prod_map, Function.comp_apply]

theorem rationalColumn_map_embedding
    (e : ι ↪ κ) (N : L[X]) (poles active : Finset ι) (x β : κ → L) (i : ι) :
    rationalColumn N (poles.map e) (active.map e) x β (e i) =
      rationalColumn N poles active (x ∘ e) (β ∘ e) i := by
  simp only [rationalColumn, Finset.mem_map', nodal_map_embedding,
    simpleResidue, nodalWeight_map_embedding, Finset.sum_map, Function.comp_apply]

/-- Multiplying the numerator by a polynomial multiplies each residue or
active evaluation by the value of that same polynomial at its row node. -/
theorem rationalColumn_mul_polynomial
    (N T : L[X]) (poles active : Finset ι) (x β : ι → L) (i : ι) :
    rationalColumn (N * T) poles active x β i =
      T.eval (x i) * rationalColumn N poles active x β i := by
  unfold rationalColumn simpleResidue
  split_ifs <;> (try simp only [eval_mul]) <;> ring

theorem nodal_insert (s : Finset κ) (x : κ → L) (a : κ) (ha : a ∉ s) :
    Lagrange.nodal (insert a s) x = (X - C (x a)) * Lagrange.nodal s x := by
  exact Finset.prod_insert ha

theorem nodalWeight_insert_other (s : Finset κ) (x : κ → L)
    (a b : κ) (ha : a ∉ s) (hab : a ≠ b) :
    Lagrange.nodalWeight (insert a s) x b =
      (x b - x a)⁻¹ * Lagrange.nodalWeight s x b := by
  have he : (insert a s).erase b = insert a (s.erase b) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hkb, hka | hks⟩
      · exact Or.inl hka
      · exact Or.inr ⟨hkb, hks⟩
    · rintro (hka | ⟨hkb, hks⟩)
      · subst k
        exact ⟨hab, Or.inl rfl⟩
      · exact ⟨hkb, Or.inr hks⟩
  rw [Lagrange.nodalWeight, he, Finset.prod_insert (by simp [ha])]
  rfl

theorem nodalWeight_insert_self (s : Finset κ) (x : κ → L)
    (a : κ) (ha : a ∉ s) :
    Lagrange.nodalWeight (insert a s) x a = ((Lagrange.nodal s x).eval (x a))⁻¹ := by
  rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Finset.erase_insert ha]

/-- The surviving rows after adding the negative first node have precisely
one extra simple denominator. No denominator nonvanishing is silently used. -/
theorem rationalColumn_insert_pole_other
    (N : L[X]) (poles active : Finset κ) (x β : κ → L)
    (a b : κ) (ha : a ∉ poles) (hab : a ≠ b) :
    rationalColumn N (insert a poles) active x β b =
      rationalColumn N poles active x β b / (x b - x a) := by
  by_cases hbA : b ∈ active
  · simp only [rationalColumn, if_pos hbA, nodal_insert poles x a ha,
      eval_mul, eval_sub, eval_X, eval_C]
    rw [div_mul_eq_div_div_swap]
  · have hmem : b ∈ insert a poles ↔ b ∈ poles := by simp [Ne.symm hab]
    simp only [rationalColumn, if_neg hbA, hmem, simpleResidue,
      nodalWeight_insert_other poles x a b ha hab]
    split_ifs <;> ring

/-- The new row is the exact weighted-normal residue, with the original
active interval unchanged. -/
theorem rationalColumn_insert_pole_self
    (N : L[X]) (poles active : Finset κ) (x β : κ → L)
    (a : κ) (ha : a ∉ poles) (haA : a ∉ active) :
    rationalColumn N (insert a poles) active x β a =
      N.eval (x a) / ((Lagrange.nodal poles x).eval (x a) * β a) *
        ∑ i ∈ active, β i / (x a - x i) := by
  simp only [rationalColumn, if_neg haA, Finset.mem_insert_self, if_true, simpleResidue,
    nodalWeight_insert_self poles x a ha, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The embedded suffix version used by the actual first-coordinate block
decomposition. -/
theorem rationalColumn_negative_suffix
    (e : ι ↪ κ) (N : L[X]) (poles active : Finset ι) (x β : κ → L)
    (a : κ) (ha : a ∉ Set.range e) (i : ι) :
    rationalColumn N (insert a (poles.map e)) (active.map e) x β (e i) =
      rationalColumn N poles active (x ∘ e) (β ∘ e) i / (x (e i) - x a) := by
  have haP : a ∉ poles.map e := by
    intro hm
    obtain ⟨j, hj, hje⟩ := Finset.mem_map.mp hm
    exact ha ⟨j, hje⟩
  have hai : a ≠ e i := fun h ↦ ha ⟨i, h.symm⟩
  rw [rationalColumn_insert_pole_other N (poles.map e) (active.map e) x β a (e i) haP hai,
    rationalColumn_map_embedding]

theorem rationalColumn_negative_new_row
    (e : ι ↪ κ) (N : L[X]) (poles active : Finset ι) (x β : κ → L)
    (a : κ) (ha : a ∉ Set.range e) :
    rationalColumn N (insert a (poles.map e)) (active.map e) x β a =
      N.eval (x a) / ((Lagrange.nodal poles (x ∘ e)).eval (x a) * β a) *
        ∑ i ∈ active, β (e i) / (x a - x (e i)) := by
  have haP : a ∉ poles.map e := by
    intro hm
    obtain ⟨j, hj, hje⟩ := Finset.mem_map.mp hm
    exact ha ⟨j, hje⟩
  have haA : a ∉ active.map e := by
    intro hm
    obtain ⟨j, hj, hje⟩ := Finset.mem_map.mp hm
    exact ha ⟨j, hje⟩
  rw [rationalColumn_insert_pole_self N (poles.map e) (active.map e) x β a haP haA,
    nodal_map_embedding, Finset.sum_map]

section Coefficients

variable {E : Type*} [Field E]

theorem nodal_map_coefficients (f : L →+* E) (s : Finset ι) (x : ι → L) :
    (Lagrange.nodal s x).map f = Lagrange.nodal s (f ∘ x) := by
  simp only [Lagrange.nodal, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Function.comp_apply]

theorem nodalWeight_map_coefficients (f : L →+* E) (s : Finset ι) (x : ι → L) (i : ι) :
    f (Lagrange.nodalWeight s x i) = Lagrange.nodalWeight s (f ∘ x) i := by
  simp only [Lagrange.nodalWeight, map_prod, map_inv₀, map_sub, Function.comp_apply]

/-- Field extension preserves the literal rational columns, including all
residue and scalar denominators. -/
theorem rationalColumn_map_coefficients
    (f : L →+* E) (N : L[X]) (poles active : Finset ι) (x β : ι → L) (i : ι) :
    f (rationalColumn N poles active x β i) =
      rationalColumn (N.map f) poles active (f ∘ x) (f ∘ β) i := by
  unfold rationalColumn simpleResidue
  rw [← nodal_map_coefficients f poles x]
  simp only [Function.comp_apply, Polynomial.eval_map_apply]
  split_ifs <;> simp only [map_div₀, map_mul, map_sum, map_sub, map_zero,
    nodalWeight_map_coefficients, Function.comp_apply]

end Coefficients

end PaperVerification.Fermion.Newton
