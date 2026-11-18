module

public import Papers.GraphicalZonotopes.ForestOscillation
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def bitVector (b : V → Bool) : V → ℝ := fun v => if b v then 1 else 0

theorem bitVector_boolean (b : V → Bool) : ∀ v,bitVector b v=0 ∨ bitVector b v=1 := by
  intro v
  cases h : b v <;> simp [bitVector,h]

theorem exists_bitVector (x : V → ℝ) (hx : ∀ v,x v=0 ∨ x v=1) :
    ∃ b : V → Bool,bitVector b=x := by
  refine ⟨fun v => decide (x v=1),?_⟩
  funext v
  rcases hx v with h | h <;> simp [bitVector,h]

/-- The integer rounding in Lemma9.3. The bounding interval may have real
endpoints; integrality is required only of the actual Boolean polynomial values. -/
theorem integral_quadratic_oscillation_lower (G : SimpleGraph V) (hG : G.IsAcyclic)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (lo hi : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      lo≤quadratic G c l w x ∧ quadratic G c l w x≤hi)
    (hint : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      ∃ k : ℤ,quadratic G c l w x=k) :
    (Int.ceil ((1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|)) : ℝ)≤hi-lo := by
  let F : (V → Bool) → ℝ := fun b => quadratic G c l w (bitVector b)
  obtain ⟨bmin,hbmin,hmin⟩ := exists_min_image (univ : Finset (V → Bool)) F univ_nonempty
  obtain ⟨bmax,hbmax,hmax⟩ := exists_max_image (univ : Finset (V → Bool)) F univ_nonempty
  obtain ⟨kmin,hkmin⟩ := hint (bitVector bmin) (bitVector_boolean bmin)
  obtain ⟨kmax,hkmax⟩ := hint (bitVector bmax) (bitVector_boolean bmax)
  have hactual : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      (kmin : ℝ)≤quadratic G c l w x ∧ quadratic G c l w x≤kmax := by
    intro x hx
    obtain ⟨b,rfl⟩ := exists_bitVector x hx
    have h₁ := hmin b (mem_univ b)
    have h₂ := hmax b (mem_univ b)
    change quadratic G c l w (bitVector bmin)≤_ at h₁
    change _≤quadratic G c l w (bitVector bmax) at h₂
    rw [hkmin] at h₁
    rw [hkmax] at h₂
    exact ⟨h₁,h₂⟩
  have hosc := quadratic_oscillation_lower G hG c l w (kmin : ℝ) (kmax : ℝ) hactual
  have hceil : Int.ceil ((1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|))≤kmax-kmin := by
    apply Int.ceil_le.mpr
    simpa only [Int.cast_sub] using hosc
  have hcast : (Int.ceil ((1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|)) : ℝ)≤
      (kmax : ℝ)-(kmin : ℝ) := by exact_mod_cast hceil
  have hminbound := (hbound (bitVector bmin) (bitVector_boolean bmin)).1
  have hmaxbound := (hbound (bitVector bmax) (bitVector_boolean bmax)).2
  rw [hkmin] at hminbound
  rw [hkmax] at hmaxbound
  linarith

end ForestSigns
end GraphicalZonotopes
