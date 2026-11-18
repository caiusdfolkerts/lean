module

public import Papers.GraphicalZonotopes.Indecomposable

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lower-support data of reflection through the origin. -/
def reflectedFunction (z : SetFunction V) (S : Finset V) : ℝ := z Sᶜ-z univ

theorem subsetSum_add_compl (x : V → ℝ) (S : Finset V) :
    subsetSum x S+subsetSum x Sᶜ=subsetSum x univ := by
  exact Finset.sum_add_sum_compl S x

@[simp] theorem subsetSum_neg (x : V → ℝ) (S : Finset V) :
    subsetSum (-x) S= -subsetSum x S := by
  simp [subsetSum]

theorem reflectedFunction_normalized (z : SetFunction V) : Normalized (reflectedFunction z) := by
  simp [Normalized,reflectedFunction]

theorem mem_basePolytope_reflected_iff {z : SetFunction V} (hz : Normalized z) (x : V → ℝ) :
    x∈basePolytope (reflectedFunction z) ↔ -x∈basePolytope z := by
  constructor
  · intro hx
    have htotal : subsetSum x univ= -z univ := by
      have h := hx.1
      simpa [reflectedFunction, show z ∅ = 0 from hz] using h
    refine ⟨by rw [subsetSum_neg,htotal,neg_neg],?_⟩
    intro S
    have h := hx.2 Sᶜ
    change z (Sᶜ)ᶜ-z univ≤subsetSum x Sᶜ at h
    rw [compl_compl] at h
    have hc := subsetSum_add_compl x S
    rw [htotal] at hc
    rw [subsetSum_neg]
    linarith
  · intro hx
    have htotal : subsetSum x univ= -z univ := by
      have h := hx.1
      rw [subsetSum_neg] at h
      linarith
    refine ⟨?_,?_⟩
    · simpa [reflectedFunction, show z ∅ = 0 from hz] using htotal
    · intro S
      have h := hx.2 Sᶜ
      rw [subsetSum_neg] at h
      have hc := subsetSum_add_compl x S
      rw [htotal] at hc
      change z Sᶜ-z univ≤subsetSum x S
      linarith

/-- Exact reflection as an equality of ordinary convex-body point sets. -/
theorem basePolytope_reflected {z : SetFunction V} (hz : Normalized z) :
    basePolytope (reflectedFunction z)=(-1 : ℝ) • basePolytope z := by
  ext x
  constructor
  · intro hx
    refine ⟨-x,(mem_basePolytope_reflected_iff hz x).mp hx,?_⟩
    simp
  · rintro ⟨y,hy,rfl⟩
    apply (mem_basePolytope_reflected_iff hz _).mpr
    simpa using hy

/-- An explicit complement identity on set functions yields the exact
translated-reflection identity for the polytopes, without geometric shortcuts. -/
theorem basePolytope_eq_translate_reflection {z w : SetFunction V}
    (hz : Normalized z) (t : V → ℝ)
    (he : reflectedFunction z=w-modular t) :
    basePolytope w=({t} : Set (V → ℝ))+(-1 : ℝ) • basePolytope z := by
  have hw : w=reflectedFunction z+modular t := by rw [he,sub_add_cancel]
  rw [hw,basePolytope_translate,basePolytope_reflected hz]

end GraphicalZonotopes
