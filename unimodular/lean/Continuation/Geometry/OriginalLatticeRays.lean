module

public import Continuation.Geometry.OriginalLatticeFan
public import TauCeti.Geometry.Toric.Algebraic.Ray.Equiv

@[expose] public section

/-!
# The exact primitive rays in the original lattice

The comparison transports primitive generators, with their signs and
integral normalization retained.  Thus the original-lattice atlas belongs
to the entire transported fan and to precisely its original ray system.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry

namespace PaperVerification.OriginalLatticeCharts

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
    [NormedAddCommGroup V] [NormedAddCommGroup V'] [NormedSpace ℝ V] [NormedSpace ℝ V']
    {ι : N →+ V} {ι' : N' →+ V'} {Φ : Fan ι} {Ψ : Fan ι'}

theorem isRay_image_of_fanEquiv (e : FanEquiv Φ Ψ) {u : N}
    (hu : Unimodular.ConeBases.IsRay Φ u) :
    Unimodular.ConeBases.IsRay Ψ (e.latticeEquiv u) := by
  obtain ⟨C, hC, ρ, hρ⟩ := hu
  exact ⟨C.map e.realEquiv.toLinearMap, (e.map_mem C).mpr hC,
    ρ.map e.realEquiv, hρ.map_equiv e.map_lattice⟩

theorem isRay_iff_image_of_fanEquiv (e : FanEquiv Φ Ψ) (u : N) :
    Unimodular.ConeBases.IsRay Φ u ↔
      Unimodular.ConeBases.IsRay Ψ (e.latticeEquiv u) := by
  constructor
  · exact isRay_image_of_fanEquiv e
  · intro hu
    have h := isRay_image_of_fanEquiv e.symm hu
    simpa only [FanEquiv.symm_latticeEquiv, AddEquiv.symm_apply_apply] using h

universe u v

variable {L : Type u} [AddCommGroup L]
    {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ L)
    {j : L →+ W} (hj : IsIntegralLattice j)
    (F : SmoothCompleteFan n)

/-- Every primitive ray, including its sign, is precisely the inverse
integral image of an original ray of the coordinate scheme fan. -/
theorem originalFan_ray_iff (w : L) :
    Unimodular.ConeBases.IsRay (originalFan b hj F) w ↔
      b.equivFun w ∈ F.rays := by
  rw [← Unimodular.FanInterfaces.dictionaryToricFan_ray_iff]
  have he : (originalFanEquiv b hj F).symm.latticeEquiv w = b.equivFun w := by
    rw [FanEquiv.symm_latticeEquiv]
    rfl
  simpa only [he] using
    isRay_iff_image_of_fanEquiv (originalFanEquiv b hj F).symm w

/-- An exact prescribed original-lattice ray set remains exact; vectors
are neither rescaled nor reoriented by the construction. -/
theorem originalFan_prescribed_rays (U : Finset L)
    (hU : ∀ v, v ∈ F.rays ↔ v ∈ U.image b.equivFun) (w : L) :
    Unimodular.ConeBases.IsRay (originalFan b hj F) w ↔ w ∈ U := by
  rw [originalFan_ray_iff, hU, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, he⟩
    exact b.equivFun.injective he ▸ hz
  · intro hw
    exact ⟨w, hw, rfl⟩

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalFan_prescribed_rays
