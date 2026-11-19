module

public import PaperVerification.AlternatingFormsBarAdmissibleCuts
public import PaperVerification.MonomialBarCuts
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The exact bar and exterior deletion signs

Both endpoints are retained in a factorization's boundary set. The
boundary at index j has exactly j earlier boundaries, so exterior
contraction deletes it with sign (-1)^j. The j=i+1 boundary is precisely
the cut merged by the i-th adjacent-product operation; its sign is the
negative normalized-bar sign. This agrees with the actual residue-tensor
differential in AlternatingFormsBarTensor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

theorem card_boundaries_before {n : ℕ} (c : Composition n)
    (j : Fin (c.length+1)) :
    (c.boundaries.filter (fun a ↦ a<c.boundary j)).card=j.val := by
  classical
  rw [Composition.boundaries,Finset.filter_map,Finset.card_map]
  have hf : Finset.univ.filter
      ((fun a : Fin (n+1) ↦ a<c.boundary j) ∘ c.boundary.toEmbedding)=Finset.Iio j := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply,
      Finset.mem_Iio]
    change c.boundary i<c.boundary j ↔ i<j
    exact c.boundary.lt_iff_lt
  rw [hf,Fin.card_Iio]

theorem boundary_erase_sign {n : ℕ} (c : Composition n)
    (j : Fin (c.length+1)) :
    TauCeti.ExteriorAlgebra.basisEraseSign (c.boundary j) c.boundaries=
      (-1 : ℤˣ)^j.val := by
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
    card_boundaries_before]

/-- Keeping the left endpoint accounts for the exact minus sign in the
residue-tensor differential, with no unspecified sign convention. -/
theorem interior_boundary_erase_sign {n : ℕ} (c : Composition n)
    (i : ℕ) (hi : i+1<c.length+1) :
    TauCeti.ExteriorAlgebra.basisEraseSign
      (c.boundary ⟨i+1,hi⟩) c.boundaries=-((-1 : ℤˣ)^i) := by
  rw [boundary_erase_sign]
  simp only [pow_succ,mul_neg,mul_one]

end PaperVerification.AlternatingForms.BarCompositions

