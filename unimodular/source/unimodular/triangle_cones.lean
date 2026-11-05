module

public import Unimodular.TriangleExtension

@[expose] public section

noncomputable section

namespace Unimodular.TriangleExtension

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The height-zero section of an extended cone recovers the old cone literally. -/
theorem mem_zero_section (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n)
    (s : Bool) (x : Ambient n) :
    Fin.cons 0 x ∈ basisCone (basis b u s) ↔ x ∈ basisCone b := by
  rw [mem_cone_iff]
  cases s <;> simp [height, residual]

theorem own_newRay_mem (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) : embed (newRay u s) ∈ basisCone (basis b u s) := by
  rw [← basis_zero b u s, mem_basisCone_iff, Unimodular.realCoordinates_basis]
  intro i
  by_cases hi : i = 0 <;> simp [Pi.single_apply, hi, eq_comm]

theorem sides_eq_of_cones_eq (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s t : Bool)
    (he : basisCone (basis b u s) = basisCone (basis c u t)) : s = t := by
  have hx := own_newRay_mem b u s
  rw [he] at hx
  have hh := ((mem_cone_iff c u t _).1 hx).1
  cases s <;> cases t
  · rfl
  · norm_num [height, newRay, embed] at hh
  · norm_num [height, newRay, embed] at hh
  · rfl

theorem old_cones_eq_of_cones_eq (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s t : Bool)
    (he : basisCone (basis b u s) = basisCone (basis c u t)) : basisCone b = basisCone c := by
  ext x
  have h := Set.ext_iff.1 he (Fin.cons 0 x)
  simpa only [mem_zero_section] using h

/-- Distinct old maximal cones give distinct new maximal cones. This prevents a count
of basis labels from being mistaken for a count of actual cones. -/
theorem cone_injective_on_maximal (old : SmoothCompleteFan n) (u : Lattice n)
    (h : Set.InjOn basisCone (↑old.maximal : Set (Module.Basis (Fin n) ℤ (Lattice n)))) :
    Set.InjOn basisCone (↑(fan old u).maximal :
      Set (Module.Basis (Fin (n + 1)) ℤ (Lattice (n + 1)))) := by
  intro B hB C hC he
  obtain ⟨b, hb, s, rfl⟩ := (mem_maximal old u _).1 hB
  obtain ⟨c, hc, t, rfl⟩ := (mem_maximal old u _).1 hC
  have hst := sides_eq_of_cones_eq b c u s t he
  have hbc := h hb hc (old_cones_eq_of_cones_eq b c u s t he)
  cases hst
  cases hbc
  rfl

/-- The number of actual geometric maximal cones doubles. -/
theorem geometric_maximal_card (old : SmoothCompleteFan n) (u : Lattice n)
    (h : Set.InjOn basisCone (↑old.maximal : Set (Module.Basis (Fin n) ℤ (Lattice n)))) :
    ((fan old u).maximal.image basisCone).card =
      2 * (old.maximal.image basisCone).card := by
  rw [Finset.card_image_of_injOn (cone_injective_on_maximal old u h),
    Finset.card_image_of_injOn h, maximal_card]

theorem zeroFan_cone_injective :
    Set.InjOn basisCone (↑zeroFan.maximal : Set (Module.Basis (Fin 0) ℤ (Lattice 0))) := by
  intro b hb c hc he
  have hb : b = Pi.basisFun ℤ (Fin 0) := by simpa [zeroFan] using hb
  have hc : c = Pi.basisFun ℤ (Fin 0) := by simpa [zeroFan] using hc
  exact hb.trans hc.symm

theorem projectiveLineFan_cone_injective :
    Set.InjOn basisCone (↑projectiveLineFan.maximal : Set (Module.Basis (Fin 1) ℤ (Lattice 1))) :=
  cone_injective_on_maximal zeroFan 0 zeroFan_cone_injective

theorem projectiveLineFan_geometric_maximal_card :
    (projectiveLineFan.maximal.image basisCone).card = 2 := by
  rw [Finset.card_image_of_injOn projectiveLineFan_cone_injective,
    projectiveLineFan_maximal_card]

end Unimodular.TriangleExtension

end
