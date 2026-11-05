module

public import Papers.GraphicalZonotopes.Mobius

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set of variables containing the support of every nonzero Möbius slot. -/
def CoefficientSupportedOn (T : Finset V) (y : SetFunction V) : Prop :=
  ∀ C : Finset V,¬C⊆T → y C=0

/-- Conditioning outside a coefficient support has no effect on any genuine
elemental difference. The endpoints need not themselves lie in the support. -/
theorem delta_zeta_inter_support {T : Finset V} {y : SetFunction V}
    (hy : CoefficientSupportedOn T y) {u v : V} (huv : u≠v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (zeta y) u v S=delta (zeta y) u v (S∩T) := by
  classical
  have hu' : u∉S∩T := fun h => hu (mem_inter.mp h).1
  have hv' : v∉S∩T := fun h => hv (mem_inter.mp h).1
  rw [zeta_eq_sum_monomials,delta_sum,delta_sum]
  apply sum_congr rfl
  intro C hC
  rw [delta_smul,delta_smul,delta_setMonomial huv hu hv,
    delta_setMonomial huv hu' hv']
  by_cases hCT : C⊆T
  · have he : C⊆insert u (insert v S) ↔ C⊆insert u (insert v (S∩T)) := by
      constructor
      · intro h w hwC
        have hw := h hwC
        simp only [mem_insert] at hw ⊢
        rcases hw with hwu | hwv | hwS
        · exact Or.inl hwu
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (mem_inter.mpr ⟨hwS,hCT hwC⟩))
      · exact fun h => h.trans (insert_subset_insert _ (insert_subset_insert _ inter_subset_left))
    simp only [he]
  · rw [hy C hCT]
    simp

/-- A variable outside the coefficient support cannot occur in a nonzero
edge slack. This uses the full Möbius transform, not a selected row family. -/
theorem delta_zeta_zero_of_outside_support {T : Finset V} {y : SetFunction V}
    (hy : CoefficientSupportedOn T y) {u v : V} (huv : u≠v)
    (huT : u∉T) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (zeta y) u v S=0 := by
  apply (nonedge_coefficients_zero_iff y huv).mpr ?_ S hu hv
  intro C huC hvC
  exact hy C (fun h => huT (h huC))

theorem delta_inter_mobius_support {T : Finset V} {z : SetFunction V}
    (hz : CoefficientSupportedOn T (mobius z)) {u v : V} (huv : u≠v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta z u v S=delta z u v (S∩T) := by
  simpa only [zeta_mobius] using delta_zeta_inter_support hz huv hu hv

theorem delta_zero_of_outside_mobius_support {T : Finset V} {z : SetFunction V}
    (hz : CoefficientSupportedOn T (mobius z)) {u v : V} (huv : u≠v)
    (huT : u∉T) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta z u v S=0 := by
  simpa only [zeta_mobius] using delta_zeta_zero_of_outside_support hz huv huT hu hv

end GraphicalZonotopes
