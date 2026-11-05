module

public import Recovery.Unimodular.WeakFano.OriginalSeedGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set TauCeti.Toric
open scoped BigOperators

namespace Unimodular.OriginalSeedGeometry
open LatticeCoordinates NormalFanCoordinateTransport

section IntegralDual
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  (ι : N →+ V)

/-- Integer evaluation is exactly restriction to an actual integral dual
homomorphism, not a substitute definition of lattice integrality. -/
theorem integralDual_iff (f : Module.Dual ℝ V) :
    (∀ x : N, ∃ z : ℤ, f (ι x) = (z : ℝ)) ↔
      ∃ l : Module.Dual ℤ N, ∀ x : N, f (ι x) = (l x : ℝ) := by
  constructor
  · intro h
    choose z hz using h
    let g : N →+ ℤ :=
      { toFun := z
        map_zero' := by
          apply Int.cast_injective (α := ℝ)
          rw [← hz 0]
          simp
        map_add' := by
          intro x y
          apply Int.cast_injective (α := ℝ)
          rw [← hz (x + y), Int.cast_add, ← hz x, ← hz y, map_add, map_add] }
    exact ⟨g.toIntLinearMap, hz⟩
  · rintro ⟨l, hl⟩ x
    exact ⟨l x, hl x⟩

end IntegralDual

section Original
variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : N →+ V}

/-- The actual convex hull in the given real realization of the lattice. -/
def originalHull (U : Finset N) : Set V := convexHull ℝ (ι '' (U : Set N))

/-- Lemma3.2 with its whole geometric conclusion on the original lattice:
the actual hull is terminal reflexive, its vertices and all lattice points
are specified exactly, its actual dual polar is a lattice polytope, and the
same complete fan is both the entire radial face fan and the entire ordinary
normal fan of that polar. No fan or polytope witness is assumed. -/
theorem lemma_3_2_original (hn : 0 < n) (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Finset N)
    (hU : IntegralRigidity.Uniform b (fun u : (U : Set N) => u.val))
    (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤) (hzero : (0 : N) ∉ U) :
    (0 : V) ∈ interior (originalHull (ι := ι) U) ∧
      (∃ s : Finset (Module.Dual ℝ V),
        (∀ f ∈ s, ∃ l : Module.Dual ℤ N, ∀ x : N, f (ι x) = (l x : ℝ)) ∧
        polar (originalHull (ι := ι) U) = convexHull ℝ (s : Set (Module.Dual ℝ V))) ∧
      (originalHull (ι := ι) U).extremePoints ℝ = ι '' (U : Set N) ∧
      (∀ x : N, ι x ∈ originalHull (ι := ι) U ↔ x = 0 ∨ x ∈ U) ∧
      ∃ Φ : Fan ι, Φ.IsComplete ∧
        AllowedBlocks.HasRays ι (fun u : (U : Set N) => u.val) Φ ∧
        (∀ C, C ∈ Φ.cones ↔ ∃ F : Set V, Convex ℝ F ∧
          IsExtreme ℝ (originalHull (ι := ι) U) F ∧
          F ≠ originalHull (ι := ι) U ∧ C = PointedCone.hull ℝ F) ∧
        (∀ C, C ∈ Φ.cones ↔ ∃ f ∈ polar (originalHull (ι := ι) U),
          C = NormalFanSupport.normalCone (polar (originalHull (ι := ι) U)) f) := by
  classical
  let : FiniteDimensional ℝ V := hι.finiteDimensional
  let eN := latticeEquiv b
  let eR := realEquiv hι b
  let UC : Finset (Lattice n) := U.image eN
  have hcoord : ∀ x : N, eR (ι x) = embed (eN x) := coordinates_commute hι b
  have hUC : (UC : Set (Lattice n)) = eN '' (U : Set N) := Finset.coe_image
  have hUc : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (UC : Set (Lattice n)) => u.val) := by
    rw [hUC]
    exact (uniform_image_iff b (U : Set N)).2 hU
  have hpc : PointedCone.hull ℝ (embed '' (UC : Set (Lattice n))) = ⊤ := by
    have h := (hull_top_coordinates_iff hι b (U : Set N)).2 hpos
    have hemb : (coordinateEmbedding n : Lattice n → Ambient n) = embed := by
      ext x i
      rfl
    simpa only [hUC, hemb] using h
  have hzc : (0 : Lattice n) ∉ UC := by
    intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.1 h
    have hz : u = 0 := eN.injective (he.trans eN.map_zero.symm)
    exact hzero (hz ▸ hu)
  obtain ⟨hzC, ⟨W, hW⟩, hexC, hpointsC, Φ, hcC, hrC, _hprimC, hfacesC, hnormalC⟩ :=
    GenericReflexivity.lemma_3_2 hn UC hUc hpc hzc
  have himages : eR '' (ι '' (U : Set N)) = embed '' (UC : Set (Lattice n)) := by
    rw [hUC, Set.image_image, Set.image_image]
    congr 1
    funext x
    exact coordinates_commute hι b x
  have hconv : eR '' originalHull (ι := ι) U = GenericReflexivity.rayHull UC := by
    calc
      eR '' convexHull ℝ (ι '' (U : Set N)) = convexHull ℝ (eR '' (ι '' (U : Set N))) :=
        eR.toLinearMap.image_convexHull _
      _ = GenericReflexivity.rayHull UC := by rw [himages]; rfl
  have hback : eR.symm '' GenericReflexivity.rayHull UC = originalHull (ι := ι) U := by
    rw [← hconv]
    simp only [Set.image_image, LinearEquiv.symm_apply_apply, Set.image_id']
  have hbackpoints : eR.symm '' (embed '' (UC : Set (Lattice n))) = ι '' (U : Set N) := by
    rw [← himages]
    simp only [Set.image_image, LinearEquiv.symm_apply_apply, Set.image_id']
  have hz : (0 : V) ∈ interior (originalHull (ι := ι) U) := by
    have hi : eR.symm '' interior (GenericReflexivity.rayHull UC) =
        interior (originalHull (ι := ι) U) := by
      have hh := eR.symm.toContinuousLinearEquiv.toHomeomorph.image_interior (GenericReflexivity.rayHull UC)
      change eR.symm '' interior (GenericReflexivity.rayHull UC) =
        interior (eR.symm '' GenericReflexivity.rayHull UC) at hh
      rwa [hback] at hh
    rw [← hi]
    exact ⟨0, hzC, eR.symm.map_zero⟩
  have hex : (originalHull (ι := ι) U).extremePoints ℝ = ι '' (U : Set N) := by
    have hh := image_extremePoints eR.symm (GenericReflexivity.rayHull UC)
    rw [hback, hexC, hbackpoints] at hh
    exact hh.symm
  have hp : ∀ x : N, ι x ∈ originalHull (ι := ι) U ↔ x = 0 ∨ x ∈ U := by
    intro x
    have hm : ι x ∈ originalHull (ι := ι) U ↔ embed (eN x) ∈ GenericReflexivity.rayHull UC := by
      constructor
      · intro hx
        have hh : eR (ι x) ∈ eR '' originalHull (ι := ι) U := ⟨ι x, hx, rfl⟩
        rw [hconv] at hh
        simpa only [hcoord] using hh
      · intro hx
        have hh : eR (ι x) ∈ eR '' originalHull (ι := ι) U := by
          rw [hconv]
          simpa only [hcoord] using hx
        exact eR.injective.mem_set_image.mp hh
    rw [hm, hpointsC]
    constructor
    · rintro (hz | hu)
      · exact Or.inl (eN.injective (hz.trans eN.map_zero.symm))
      · obtain ⟨y, hy, he⟩ := Finset.mem_image.1 hu
        exact Or.inr (eN.injective he ▸ hy)
    · rintro (rfl | hu)
      · exact Or.inl eN.map_zero
      · exact Or.inr (Finset.mem_image.2 ⟨x, hu, rfl⟩)
  let s : Finset (Module.Dual ℝ V) :=
    W.image (fun w => dualTransport eR.symm (coordinateDual (embed w)))
  have hs : (s : Set (Module.Dual ℝ V)) =
      dualTransport eR.symm '' (coordinateDual '' (embed '' (W : Set (Lattice n)))) := by
    simp only [s, Finset.coe_image, Set.image_image]
  have hint : ∀ f ∈ s, ∃ l : Module.Dual ℤ N, ∀ x : N, f (ι x) = (l x : ℝ) := by
    intro f hf
    apply (integralDual_iff ι f).mp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hf
    intro x
    refine ⟨∑ i, w i * eN x i, ?_⟩
    change coordinateDual (embed w) (eR (ι x)) = _
    rw [show eR (ι x) = embed (eN x) from coordinates_commute hι b x]
    exact coordinateDual_integral w (eN x)
  have hpolar : polar (originalHull (ι := ι) U) =
      convexHull ℝ (s : Set (Module.Dual ℝ V)) := by
    rw [← hback, polar_image, coordinate_polar, hW, hs]
    have hCD : coordinateDual '' convexHull ℝ (embed '' (W : Set (Lattice n))) =
        convexHull ℝ (coordinateDual '' (embed '' (W : Set (Lattice n)))) :=
      coordinateDual.toLinearMap.image_convexHull _
    rw [hCD]
    exact (dualTransport eR.symm).toLinearMap.image_convexHull _
  have hcomm : ∀ x : N, eR (ι x) = FanBridge.standardEmbedding n (eN x) :=
    coordinates_commute hι b
  have hcommBack : ∀ x : Lattice n, eR.symm (FanBridge.standardEmbedding n x) =
      ι (eN.symm x) := FanTransport.compatible_inverse eN.toAddEquiv eR hcomm
  let Ψ := FanTransport.transport eN.toAddEquiv.symm eR.symm hcommBack Φ
  let ε : FanEquiv Φ Ψ := FanTransport.equivalence eN.toAddEquiv.symm eR.symm hcommBack Φ
  have hlabel : AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
      (fun u : (U : Set N) => eN u.val) Φ := by
    intro C
    rw [hrC C]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu, he⟩ := Finset.mem_image.1 v.property
      exact ⟨⟨u, hu⟩, by simpa only [he] using hv⟩
    · rintro ⟨u, hu⟩
      exact ⟨⟨eN u.val, Finset.mem_image.2 ⟨u.val, u.property, rfl⟩⟩, hu⟩
  have hnormalDual : ∀ C, C ∈ Φ.cones ↔ ∃ f ∈ polar (GenericReflexivity.rayHull UC),
      C = NormalFanSupport.normalCone (polar (GenericReflexivity.rayHull UC)) f := by
    intro C
    rw [coordinate_polar]
    constructor
    · intro hC
      obtain ⟨z, hz, he⟩ := (hnormalC C).mp hC
      exact ⟨coordinateDual z, ⟨z, hz, rfl⟩, he.trans (coordinate_normalCone _ _).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, he⟩
      exact (hnormalC C).mpr ⟨z, hz, he.trans (coordinate_normalCone _ _)⟩
  refine ⟨hz, ⟨s, hint, hpolar⟩, hex, hp, Ψ, ε.isComplete_iff.2 hcC, ?_, ?_, ?_⟩
  · apply FanTransport.hasRays_of_equiv ε (u := fun u : (U : Set N) => eN u.val)
      (u' := fun u : (U : Set N) => u.val) _ hlabel
    intro u
    change eR.symm (FanBridge.standardEmbedding n (eN u.val)) = ι u.val
    rw [hcommBack, eN.symm_apply_apply]
  · have hh := radial_fan_transport ε (GenericReflexivity.rayHull UC) hfacesC
    change ∀ C, C ∈ Ψ.cones ↔ _ at hh
    simpa only [show ε.realEquiv = eR.symm from rfl, hback] using hh
  · have hh := polar_normal_fan_transport ε (GenericReflexivity.rayHull UC) hnormalDual
    simpa only [show ε.realEquiv = eR.symm from rfl, hback] using hh

end Original
end Unimodular.OriginalSeedGeometry

#print axioms Unimodular.OriginalSeedGeometry.integralDual_iff
#print axioms Unimodular.OriginalSeedGeometry.lemma_3_2_original
#check Unimodular.OriginalSeedGeometry.lemma_3_2_original
