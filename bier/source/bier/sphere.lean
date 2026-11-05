import bier.cone_complex

/-!
# Bier's sphere theorem

The canonical coned realization embeds by the signed coordinate projection
modulo the diagonal. Its image contains a neighborhood of the apex. The
geometric link theorem therefore supplies a genuine piecewise affine sphere,
and inverse simplicial vertex maps identify that link with the deleted join.
-/

noncomputable section

namespace Bier

open Set Geometry Topology
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

namespace Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSphere (K : Complex V) (n : ℕ) : Prop :=
  IsPLSphere n (standardRealization K.toAbstract).space

theorem isSphere_of_cone_link (K : Complex V) {n : ℕ}
    (h : IsPLSphere n
      (DifferentialGeometry.Topology.SimplicialComplex.geometricLink
        (standardRealization K.cone.toAbstract) {Pi.single none (1 : ℝ)}).space) :
    K.IsSphere n := by
  classical
  change IsPLSphere n
    (DifferentialGeometry.Topology.SimplicialComplex.geometricLink
      (standardRealization K.cone.toAbstract) {Cubical.PL.standardVertex none}).space at h
  rw [← Cubical.PL.standardRealization_link_singleton, cone_link_abstract] at h
  let v : V → Option V → ℝ := fun i => Pi.single (some i) 1
  have hv : Function.Injective v := fun i j heq =>
    Option.some_injective _ (Cubical.PL.standardVertex_injective heq)
  have hfaces : (standardRealization (K.toAbstract.map some)).faces =
      (@PreAbstractSimplicialComplex.map V (Option V → ℝ)
        (fun a b => Classical.propDecidable (a = b)) K.toAbstract v).faces := by
    ext s
    constructor
    · rintro ⟨t, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u, hu, ?_⟩
      apply Finset.coe_injective
      simp only [Finset.coe_image, Set.image_image]
      rfl
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.image some, ⟨u, hu, rfl⟩, ?_⟩
      apply Finset.coe_injective
      simp only [Finset.coe_image, Set.image_image]
      rfl
  obtain ⟨f, hf⟩ := Cubical.PL.exists_isPLHomeomorphOn_realization K.toAbstract v hv
    (standardRealization (K.toAbstract.map some)) hfaces
  exact h.of_isPLHomeomorphOn hf.symm

/-- Every proper finite complex on at least two labels has its full Bier
deleted join PL-homeomorphic to the sphere of dimension `|V| - 2`.
Singleton faces are not assumed: ghost labels are included. -/
theorem bier_isSphere (K : Complex V) (hK : K.Proper) (hcard : 2 ≤ Fintype.card V) :
    (K.bier hK).IsSphere (Fintype.card V - 2) := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v₀ : V := Classical.choice hne
  let C := standardRealization (K.bier hK).cone.toAbstract
  letI : Finite C.faces := (standardRealization_finite_faces _).to_subtype
  have hcoordinates : C.space = {w | ConeCoordinates K.face w} := by
    ext w
    exact bier_cone_coordinates K hK w
  have hinj : Set.InjOn (coneProjection v₀) C.space := by
    rw [hcoordinates]
    exact coneProjection_injective K.face (fun h h' => K.downward h h') v₀
  obtain ⟨L, hfinite, hspace, hiso⟩ := exists_linear_image_glueIso C (coneProjection v₀) hinj
  letI : Finite L.faces := hfinite.to_subtype
  let p : Option (V ⊕ V) → ℝ := Pi.single none 1
  have hp : {p} ∈ C.faces := cone_apex_face (K.bier hK)
  have hzero : coneProjection v₀ p = 0 := by
    ext v
    simp [p, signedCoordinate]
  have hpL : {0} ∈ L.faces := hzero ▸ hiso.singleton_mem hp
  have hnhds : L.space ∈ 𝓝 (0 : {v : V // v ≠ v₀} → ℝ) := by
    rw [hspace, hcoordinates]
    exact coneProjection_image_mem_nhds K.face K.empty (fun h h' => K.downward h h') hK v₀
  have hdim : Module.finrank ℝ ({v : V // v ≠ v₀} → ℝ) = Fintype.card V - 2 + 1 := by
    rw [Module.finrank_pi]
    have hc : Fintype.card {v : V // v ≠ v₀} = Fintype.card V - 1 := by
      simpa using (Fintype.card_subtype_compl (fun v : V => v = v₀))
    omega
  have hsphere := isPLSphere_geometricLink_of_mem_nhds hdim L hpL hnhds
  apply isSphere_of_cone_link (K.bier hK)
  apply hiso.isPLSphere_geometricLink hp
  simpa only [hzero] using hsphere

end Complex
end Bier
