import cubical.polytope.graph
import cubical.polytope.connettivita_globale
import Mathlib.Order.Interval.Set.Monotone

/-!
# Combinatorial equivalences preserve geometric face dimension

An order isomorphism of nonempty geometric face posets already preserves
dimension. The proof uses complete flags and strict growth of affine
dimension along a proper inclusion of exposed faces. Thus no separate rank
preservation assumption is needed in the definition of a cubical polytope.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

theorem faceOrderIso_dimension_le (φ : FaceType P ≃o FaceType Q)
    (F : FaceType P) : faceDim F.val ≤ faceDim (φ F).val := by
  classical
  let d := faceDim F.val
  obtain ⟨c, hcd, hcface, hcmono⟩ := chain_ending_at_face P F.property (d := d) rfl
  let C (k : ℕ) : FaceType P :=
    if hk : k ≤ d then ⟨c k, (hcface k hk).1⟩ else F
  have hC (k : ℕ) (hk : k ≤ d) : (C k).val = c k := by
    simp only [C, dif_pos hk]
  have hCd : C d = F := by
    apply Subtype.ext
    exact (hC d le_rfl).trans hcd
  have hstrict : StrictMonoOn (fun k => faceDim (φ (C k)).val) (Iic d) := by
    intro i hi j hj hij
    apply faceDim_lt_of_ssubset Q (φ (C i)).property (φ (C j)).property
    have hCij : C i < C j := by
      change (C i).val ⊂ (C j).val
      rw [hC i hi, hC j hj]
      exact hcmono i j hij hj
    exact φ.strictMono hCij
  have hbound := hstrict.Iic_id_le d le_rfl
  simpa only [hCd, d] using hbound

/-- Combinatorial equivalence of ordinary face posets preserves dimension. -/
theorem faceOrderIso_dimension (φ : FaceType P ≃o FaceType Q)
    (F : FaceType P) : faceDim (φ F).val = faceDim F.val := by
  apply le_antisymm
  · simpa using faceOrderIso_dimension_le φ.symm (φ F)
  · exact faceOrderIso_dimension_le φ F

end LeanEval.Geometry.PlatonicClassification
