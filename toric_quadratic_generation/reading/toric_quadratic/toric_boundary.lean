module
public import PaperVerification.ToricIntegralAffine
public import Mathlib.Topology.Order.Basic
@[expose] public section
/-!
# Boundary points lie on proper actual faces

A finite halfspace presentation is constructed earlier from finite convex hulls.
Here globally redundant equality constraints are removed using full dimension,
so an ordinary boundary point yields a genuinely proper convex face.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]

/-- An affine functional vanishing on a set vanishes throughout its affine span. -/
theorem affine_zero_on_span (S : Set V) (f : V →ᵃ[ℝ] ℝ)
    (h : ∀ x ∈ S, f x = 0) : ∀ x ∈ affineSpan ℝ S, f x = 0 := by
  intro x hx
  refine affineSpan_induction (p := fun y => f y = 0) hx h ?_
  intro c u v w hu hv hw
  rw [AffineMap.map_vadd, map_smul, AffineMap.linear_apply_vsub]
  simp [hu, hv, hw]

namespace AffineInequalities

variable (H : AffineInequalities I V) [Finite I]

/-- A noninterior point of a full-dimensional finite halfspace polytope
has an active supporting constraint that is not globally redundant. -/
theorem exists_informative_active_of_not_interior
    (hspan : affineSpan ℝ H.region = ⊤) (x : V) (hx : x ∈ H.region)
    (hint : x ∉ interior H.region) :
    ∃ i : I, H.informative i ∧ H.slack i x = 0 := by
  classical
  by_contra h
  have hstrict (i : I) (hi : H.informative i) : 0 < H.slack i x := by
    have hne : H.slack i x ≠ 0 := fun hz => h ⟨i, hi, hz⟩
    exact lt_of_le_of_ne (hx i) hne.symm
  have hzero (i : I) (hi : ¬ H.informative i) : ∀ y : V, H.slack i y = 0 := by
    intro y
    have hz : ∀ z ∈ H.region, H.slack i z = 0 := by
      intro z hz
      by_contra hne
      exact hi ⟨z, hz, hne⟩
    exact affine_zero_on_span H.region (H.slack i) hz y (by rw [hspan]; trivial)
  let U : Set V := ⋂ i : {i : I // H.informative i}, {y | 0 < H.slack i.1 y}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (H.continuous_slack i.1)
  have hxU : x ∈ U := mem_iInter.mpr (fun i => hstrict i.1 i.2)
  have hUH : U ⊆ H.region := by
    intro y hy i
    by_cases hi : H.informative i
    · exact (mem_iInter.mp hy ⟨i, hi⟩).le
    · exact le_of_eq (hzero i hi y).symm
  exact hint (interior_maximal hUH hU hxU)

/-- A boundary point lies on a proper ordinary convex face. -/
theorem exists_proper_face_of_not_interior
    (hspan : affineSpan ℝ H.region = ⊤) (x : V) (hx : x ∈ H.region)
    (hint : x ∉ interior H.region) :
    ∃ F : Set V, x ∈ F ∧ Convex ℝ F ∧ IsExtreme ℝ H.region F ∧ F ≠ H.region := by
  obtain ⟨i, hi, hix⟩ := H.exists_informative_active_of_not_interior hspan x hx hint
  refine ⟨H.face {i}, ⟨hx, ?_⟩, H.convex_face {i}, H.isExtreme_face {i}, ?_⟩
  · intro j hj
    simpa only [Set.mem_singleton_iff.mp hj] using hix
  · obtain ⟨y, hy, hiy⟩ := hi
    intro hface
    have hyface : y ∈ H.face {i} := by rw [hface]; exact hy
    exact hiy (hyface.2 i (Set.mem_singleton i))

end AffineInequalities

end PaperVerification.ToricExchange

namespace PaperVerification.ToricGeometry.LatticePolytope

open PaperVerification.ToricExchange

/-- The boundary-face reduction for the literal full-dimensional lattice
polytope type, with no exposed-face assumption. -/
theorem boundary_proper_face {n : ℕ} (P : LatticePolytope n)
    (x : Ambient n) (hx : x ∈ P.carrier) (hint : x ∉ interior P.carrier) :
    ∃ F : Set (Ambient n), x ∈ F ∧ Convex ℝ F ∧
      IsExtreme ℝ P.carrier F ∧ F ≠ P.carrier := by
  obtain ⟨I, hI, H, hP⟩ := P.hasFiniteHalfspaces
  letI := hI
  have hspan : affineSpan ℝ H.region = ⊤ := by
    rw [← hP]
    exact P.fullDimensional
  rw [hP] at hx hint ⊢
  exact H.exists_proper_face_of_not_interior hspan x hx hint

end PaperVerification.ToricGeometry.LatticePolytope
