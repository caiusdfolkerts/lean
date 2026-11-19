module

public import PaperVerification.AlternatingFormsOddOrbitInterleaving
public import PaperVerification.AlternatingFormsOddWalkCount

/-!
# The actual odd generic quotient has the paper's complete walk series

This combines the explicit dominant orbit of the literal odd pencil, the
actual good exterior basis after its proved coordinate permutation, and
the bijection with the paper's bounded walks.  The single coefficient
polynomial controls every exterior degree simultaneously.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

theorem odd_actual_generic_hilbert (t : ℕ) :
    ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
      ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 → ∀ s : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) =
          StripWalks.paperWalkCount (2*(t+1)+1) s := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨Q, hbase, hQ⟩ := oddOrbit_actual_hilbert_certificate (K := K) t
  refine ⟨Q, ?_, ?_⟩
  · intro hz
    exact hbase (by rw [hz, map_zero])
  · intro y hy s
    rw [hQ y hy s, oddOrbitQuotientDegree_finrank,
      card_goodOddIndex_eq_paperWalkCount]

theorem odd_actual_generic_paperHilbert (t : ℕ) :
    ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
      ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 →
        (∀ s : ℕ, Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) =
          StripWalks.paperWalkCount (2*(t+1)+1) s) ∧
        (∀ s : ℕ, t+2 < s →
          Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
            (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) = 0) := by
  obtain ⟨Q, hQ, h⟩ := odd_actual_generic_hilbert (K := K) t
  refine ⟨Q, hQ, ?_⟩
  intro y hy
  refine ⟨h y hy, ?_⟩
  intro s hs
  rw [h y hy s, paperWalkCount_odd_above_cutoff (t+1) s (by omega)]

end PaperVerification.AlternatingForms
