module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! UNVERIFIED coordinate transport of actual toric fans. This is used to
justify the coordinate root model against the literal zero-sum lattice,
including its entire cone family, completeness and integral regularity. -/

namespace Unimodular.FanTransport

open TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {ι : N →+ V} {ι' : N' →+ V'}

theorem map_inverse (e : V ≃ₗ[ℝ] V') (C : PointedCone ℝ V) :
    (C.map (e : V →ₗ[ℝ] V')).map (e.symm : V' →ₗ[ℝ] V) = C := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, he⟩
    have hzx : z = x := by simpa using he
    exact hzx ▸ hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

theorem map_inverse_rev (e : V ≃ₗ[ℝ] V') (C : PointedCone ℝ V') :
    (C.map (e.symm : V' →ₗ[ℝ] V)).map (e : V →ₗ[ℝ] V') = C := by
  simpa only [LinearEquiv.symm_symm] using map_inverse e.symm C

theorem map_injective (e : V ≃ₗ[ℝ] V') :
    Function.Injective (fun C : PointedCone ℝ V => C.map (e : V →ₗ[ℝ] V')) := by
  intro C D he
  have h := congrArg (fun F => F.map (e.symm : V' →ₗ[ℝ] V)) he
  simpa only [map_inverse] using h

theorem map_inf (e : V ≃ₗ[ℝ] V') (C D : PointedCone ℝ V) :
    (C ⊓ D).map (e : V →ₗ[ℝ] V') = C.map e ⊓ D.map e := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyD⟩, rfl⟩
    exact ⟨⟨y, hyC, rfl⟩, ⟨y, hyD, rfl⟩⟩
  · rintro ⟨⟨y, hy, hey⟩, ⟨z, hz, hez⟩⟩
    have he : y = z := e.injective (hey.trans hez.symm)
    exact ⟨y, ⟨hy, he.symm ▸ hz⟩, hey⟩

theorem compatible_inverse (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (ι n) = ι' (f n)) :
    ∀ n', e.symm (ι' n') = ι (f.symm n') := by
  intro n'
  apply e.injective
  simpa using (hfe (f.symm n')).symm

def transport (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (ι n) = ι' (f n)) (Φ : Fan ι) : Fan ι' where
  lattice := (isIntegralLattice_congr f e hfe).mp Φ.lattice
  cones := (fun C : PointedCone ℝ V => C.map (e : V →ₗ[ℝ] V')) '' Φ.cones
  finite_cones := Φ.finite_cones.image _
  isToricCone := by
    rintro D ⟨C, hC, rfl⟩
    exact (Φ.isToricCone hC).map (f := f.toAddMonoidHom) hfe e.injective
  mem_of_isFaceOf := by
    rintro D F ⟨C, hC, rfl⟩ hF
    have hback := hF.map (e.symm : V' →ₗ[ℝ] V) e.symm.injective
    rw [map_inverse] at hback
    exact ⟨F.map (e.symm : V' →ₗ[ℝ] V), Φ.mem_of_isFaceOf hC hback,
      map_inverse e.symm F⟩
  inf_isFaceOf_left := by
    rintro C' D' ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    rw [← map_inf]
    exact (Φ.inf_isFaceOf_left hC hD).map (e : V →ₗ[ℝ] V') e.injective

def equivalence (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (ι n) = ι' (f n)) (Φ : Fan ι) :
    FanEquiv Φ (transport f e hfe Φ) where
  latticeEquiv := f
  realEquiv := e
  map_lattice := hfe
  map_mem C := by
    constructor
    · rintro ⟨D, hD, he⟩
      exact (map_injective e he) ▸ hD
    · intro hC
      exact ⟨C, hC, rfl⟩

theorem transport_complete_iff (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (ι n) = ι' (f n)) (Φ : Fan ι) :
    (transport f e hfe Φ).IsComplete ↔ Φ.IsComplete := (equivalence f e hfe Φ).isComplete_iff

theorem transport_regular_iff (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (ι n) = ι' (f n)) (Φ : Fan ι) :
    (transport f e hfe Φ).IsRegular ↔ Φ.IsRegular := (equivalence f e hfe Φ).isRegular_iff

theorem transport_inverse (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (ι n) = ι' (f n)) (Φ : Fan ι) :
    transport f.symm e.symm (compatible_inverse f e hfe) (transport f e hfe Φ) = Φ := by
  apply Fan.ext
  ext C
  constructor
  · rintro ⟨D, ⟨E, hE, rfl⟩, rfl⟩
    change (E.map (e : V →ₗ[ℝ] V')).map (e.symm : V' →ₗ[ℝ] V) ∈ Φ.cones
    rwa [map_inverse]
  · intro hC
    exact ⟨C.map (e : V →ₗ[ℝ] V'), ⟨C, hC, rfl⟩, map_inverse e C⟩

/-- A true bijection on all fans under a fixed integral change of
coordinates; it is not restricted to chosen examples or simplicial fans. -/
def fansEquiv (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (ι n) = ι' (f n)) : Fan ι ≃ Fan ι' where
  toFun := transport f e hfe
  invFun := transport f.symm e.symm (compatible_inverse f e hfe)
  left_inv := transport_inverse f e hfe
  right_inv Ψ := by
    apply Fan.ext
    ext C
    constructor
    · rintro ⟨D, ⟨E, hE, rfl⟩, rfl⟩
      change (E.map (e.symm : V' →ₗ[ℝ] V)).map (e : V →ₗ[ℝ] V') ∈ Ψ.cones
      simpa only [map_inverse_rev] using hE
    · intro hC
      exact ⟨C.map (e.symm : V' →ₗ[ℝ] V), ⟨C, hC, rfl⟩, map_inverse e.symm C⟩

end Unimodular.FanTransport

#print axioms Unimodular.FanTransport.transport
#print axioms Unimodular.FanTransport.fansEquiv
#print axioms Unimodular.FanTransport.transport_complete_iff
#print axioms Unimodular.FanTransport.transport_regular_iff
