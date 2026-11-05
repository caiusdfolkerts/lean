import bier.geometry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Normalizing a simplex facet and an outside vertex

The coordinate model is derived from a genuine convex realization. Its
supporting functionals and affine independence are transported through an
actual linear basis of the polytope's directional span.
-/

noncomputable section

namespace Bier

open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

structure CoordinateModel (K : Complex V) (I : Type*) [Fintype I] where
  point : ↥K.vertices → (I → ℝ)
  affineIndependent : ∀ (s : Finset ↥K.vertices), K.face (s.image Subtype.val) →
    s.Nonempty → AffineIndependent ℝ (fun v : s => point v.val)
  supporting : ∀ (s : Finset ↥K.vertices), K.face (s.image Subtype.val) → s.Nonempty →
    ∃ (l : (I → ℝ) →ₗ[ℝ] ℝ) (c : ℝ),
      (∀ v, l (point v) ≤ c) ∧ (∀ v, l (point v) = c ↔ v ∈ s)

namespace PolytopeRealization

variable {K : Complex V} {n : ℕ} (r : PolytopeRealization K n)

theorem normalized_coordinates [Nonempty I] (p : I → ↥K.vertices)
    (hp : Function.Injective p) (z : ↥K.vertices) (hz : z ∉ Finset.univ.image p)
    (hface : K.face ((Finset.univ.image p).image Subtype.val))
    (hdim : r.polytope.dim = Fintype.card I) :
    ∃ M : CoordinateModel K I, M.point z = 0 ∧ ∀ i, M.point (p i) = Pi.single i 1 := by
  let s := Finset.univ.image p
  have hs : s.Nonempty := Finset.univ_nonempty.image p
  have hAIp : AffineIndependent ℝ (fun i => r.point (p i)) := by
    let e : I ↪ s := ⟨fun i => ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩,
      fun i j h => hp (congrArg Subtype.val h)⟩
    exact (r.face_affineIndependent hface hs).comp_embedding e
  obtain ⟨l, c, _, hl⟩ := r.supporting_functional hface hs
  have hlp (i : I) : l (r.point (p i)) = c :=
    (hl _).mpr (Finset.mem_image_of_mem p (Finset.mem_univ i))
  have hlz : l (r.point z) ≠ c := fun he => hz ((hl z).mp he)
  have hLI := linearIndependent_of_affineIndependent_supporting
    (fun i => r.point (p i)) (r.point z) hAIp l.toLinearMap c hlp hlz
  let D := vectorSpan ℝ r.polytope.toSet
  let v : ↥K.vertices → D := fun a =>
    ⟨r.point a - r.point z, vsub_mem_vectorSpan ℝ (r.point_mem_polytope a)
      (r.point_mem_polytope z)⟩
  have hLIv : LinearIndependent ℝ (fun i => v (p i)) :=
    LinearIndependent.of_comp D.subtype hLI
  have hcard : Fintype.card I = Module.finrank ℝ D := hdim.symm
  let b := basisOfLinearIndependentOfCardEqFinrank' (fun i => v (p i)) hLIv hcard
  have hb (i : I) : b i = v (p i) := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i
  let X : ↥K.vertices → (I → ℝ) := fun a => b.equivFun (v a)
  let L : (I → ℝ) →ₗ[ℝ] E n := D.subtype.comp b.equivFun.symm.toLinearMap
  have hLX (a : ↥K.vertices) : L (X a) = r.point a - r.point z := by
    simp [L, X, v]
  let F : (I → ℝ) →ᵃ[ℝ] E n :=
    { toFun := fun x => L x + r.point z
      linear := L
      map_vadd' := by intro x y; simp [map_add, add_assoc] }
  have hFX (a : ↥K.vertices) : F (X a) = r.point a := by
    change L (X a) + r.point z = _
    rw [hLX, sub_add_cancel]
  let M : CoordinateModel K I :=
    { point := X
      affineIndependent := by
        intro t ht htn
        apply AffineIndependent.of_comp F
        change AffineIndependent ℝ (fun v : t => F (X v.val))
        simpa only [hFX] using r.face_affineIndependent ht htn
      supporting := by
        intro t ht htn
        obtain ⟨f, c, hle, he⟩ := r.supporting_functional ht htn
        refine ⟨f.toLinearMap.comp L, c - f (r.point z), ?_, ?_⟩
        · intro a
          change f (L (X a)) ≤ c - f (r.point z)
          rw [hLX, map_sub]
          linarith [hle a]
        · intro a
          change f (L (X a)) = c - f (r.point z) ↔ _
          rw [hLX, map_sub, sub_left_inj]
          exact he a }
  refine ⟨M, ?_, ?_⟩
  · change b.equivFun (v z) = 0
    have hv : v z = 0 := by apply Subtype.ext; simp [v]
    rw [hv, map_zero]
  · intro i
    change b.equivFun (v (p i)) = _
    rw [← hb]
    funext j
    simpa [Pi.single_apply, eq_comm] using b.equivFun_self i j

end PolytopeRealization
end Bier
