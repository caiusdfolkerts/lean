import cubical.rigidity
import cubical.local_propagation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean rigidity supplies the local pinned condition

This bridges the actual geometric rigidity definition to the coordinate
equations used in the local polynomial matrix.  The selected pins must be
affinely independent and number at least the ambient dimension.
-/

namespace Cubical.Local

open scoped RealInnerProductSpace

theorem pinnedRigid_of_rigid
    {B L T : Type*} [Fintype L] [Fintype T] [Nonempty T]
    (k : ℕ) (G : SimpleGraph B) (left right : L → B) (pin : T → B)
    (hedges : ∀ a b, G.Adj a b → ∃ e,
      (left e = a ∧ right e = b) ∨ (left e = b ∧ right e = a))
    (q : B → EuclideanSpace ℝ (Fin k)) (hq : Rigidity.IsRigid G q)
    (hpins : AffineIndependent ℝ (q ∘ pin)) (hcard : k ≤ Fintype.card T) :
    PinnedRigid k left right pin (fun b i ↦ q b i) := by
  intro v hv hpin
  let u : B → EuclideanSpace ℝ (Fin k) :=
    fun b ↦ (EuclideanSpace.equiv (Fin k) ℝ).symm (v b)
  have hcoord (a b : B) :
      inner ℝ (q a - q b) (u a - u b) =
        ∑ i, (q a i - q b i) * (v a i - v b i) := by
    simp [PiLp.inner_apply, u, mul_comm]
  have hm : Rigidity.IsMotion G q u := by
    intro a b hab
    rw [hcoord]
    obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hedges a b hab
    · exact hv e
    · convert hv e using 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  obtain ⟨t, A, hA, hu⟩ := hq u hm
  have hpin' : ∀ a : T, t + A ((q ∘ pin) a) = 0 := by
    intro a
    rw [Function.comp_apply, ← hu]
    ext i
    exact congrFun (hpin a) i
  have hz := Pinning.rigid_motion_pinned_on_affine_independent
    A t (q ∘ pin) hA hpins (by simpa using hcard) hpin'
  funext b i
  have hb : u b = 0 := (hu b).trans (hz.2.2 (q b))
  exact congrArg (fun x : EuclideanSpace ℝ (Fin k) ↦ x i) hb

end Cubical.Local
