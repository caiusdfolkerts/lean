import cubical.abstract_bound

/-! # An enumeration-independent interface to the rank bound

`Nat.card` avoids identifying two computational enumerations of a deeply
nested geometric incidence subtype. It is proved equal to `Fintype.card`.
-/

namespace Cubical.FacetCover

open Classical
attribute [local instance] Classical.propDecidable

variable {B W E F : Type*} {black : E → B} {white : E → W}
variable [Fintype B] [Fintype W] [Fintype E] [Fintype F]

/-- A common polynomial certificate, with enumeration-independent incidence
counts, proves local propagation, facet determination and the exact facet
nullity simultaneously. -/
theorem StarCover.generic_facet_certificate_intrinsic
    {C : Cubical.FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Cubical.Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k)))
    (hwhite : ∀ f (b : {b : B // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white e.val.val))
    (hdegree : ∀ f (b : {b : B // C.blackMem f b}), Nat.card (C.EdgeAtBlack f b) ≤ k + 1)
    (hblack_count : ∀ f, Nat.card {b : B // C.blackMem f b} = 2 ^ (k - 1))
    (hwhite_count : ∀ f, Nat.card {w : W // C.whiteMem f w} = 2 ^ (k - 1))
    (hedge_count : ∀ f, Nat.card {e : E // C.edgeMem f e} = k * 2 ^ (k - 1)) :
    ∃ Q : MvPolynomial (W × Fin (k + 1)) ℝ, Q ≠ 0 ∧
      ∀ x : W × Fin (k + 1) → ℝ, MvPolynomial.eval x Q ≠ 0 →
        C.LocalPropagation (k + 1) (fun w i => x (w, i)) ∧
        (∀ f, Function.Injective (C.restriction (k + 1) (fun w i => x (w, i)) f)) ∧
        (∀ f, Module.finrank ℝ (Cubical.solutionSpace (k + 1)
          (C.facetBlack f) (C.facetWhite f)
          (fun w : {w : W // C.whiteMem f w} => fun i => x (w.val, i))) = 2 ^ k) := by
  have hdegree' : ∀ f (b : {b : B // C.blackMem f b}),
      Fintype.card (C.EdgeAtBlack f b) ≤ k + 1 := by
    intro f b
    rw [← Nat.card_eq_fintype_card]
    exact hdegree f b
  obtain ⟨Q, hQ, hgeneric⟩ := D.generic_parameters k hk hpin hlink hwhite hdegree'
  refine ⟨Q, hQ, ?_⟩
  intro x hx
  obtain ⟨hprop, hind⟩ := hgeneric x hx
  refine ⟨hprop, fun f => C.restriction_injective (k + 1) _ hprop f, ?_⟩
  intro f
  have hb : Fintype.card {b : B // C.blackMem f b} = 2 ^ (k - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hblack_count f
  have hw : Fintype.card {w : W // C.whiteMem f w} = 2 ^ (k - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hwhite_count f
  have he : Fintype.card {e : E // C.edgeMem f e} = k * 2 ^ (k - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hedge_count f
  have h := Cubical.balanced_facet_dimension k (2 ^ (k - 1))
    (C.facetBlack f) (C.facetWhite f)
    (fun w : {w : W // C.whiteMem f w} => fun i => x (w.val, i))
    (hind f) hb hw he
  have hpow : 2 * 2 ^ (k - 1) = 2 ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp [pow_succ, Nat.mul_comm]
  exact h.trans hpow

theorem StarCover.asymmetric_edge_bound_intrinsic
    {C : Cubical.FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Cubical.Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k)))
    (hwhite : ∀ f (b : {b : B // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white e.val.val))
    (hdegree : ∀ f (b : {b : B // C.blackMem f b}), Nat.card (C.EdgeAtBlack f b) ≤ k + 1)
    (hblack_count : ∀ f, Nat.card {b : B // C.blackMem f b} = 2 ^ (k - 1))
    (hwhite_count : ∀ f, Nat.card {w : W // C.whiteMem f w} = 2 ^ (k - 1))
    (hedge_count : ∀ f, Nat.card {e : E // C.edgeMem f e} = k * 2 ^ (k - 1))
    (f : F) :
    (k + 1) * Fintype.card B + Fintype.card W ≤ Fintype.card E + 2 ^ k := by
  apply D.asymmetric_edge_bound k hk hpin hlink hwhite
  · intro f b
    rw [← Nat.card_eq_fintype_card]
    exact hdegree f b
  · intro f
    rw [← Nat.card_eq_fintype_card]
    exact hblack_count f
  · intro f
    rw [← Nat.card_eq_fintype_card]
    exact hwhite_count f
  · intro f
    rw [← Nat.card_eq_fintype_card]
    exact hedge_count f
  · exact f

end Cubical.FacetCover
