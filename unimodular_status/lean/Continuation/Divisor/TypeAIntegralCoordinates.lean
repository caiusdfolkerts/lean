module

public import Continuation.Divisor.NefClosure

/-!
# The type-A conclusion in every integral coordinate system

The root set may be the image of the standard type-A roots under any
integral linear equivalence. The proof constructs supporting cut forms
on the original fan, so the resulting nefness and bigness concern its
original scheme and intrinsic anticanonical line bundle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace Unimodular.TypeABoundary

open PaperVerification.ToricGeometry
variable {n : ℕ}

/-- Simplex vertices in an arbitrary integral basis. -/
def rootVertexInBasis (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Option (Fin n) → Lattice n
  | none => 0
  | some i => b i

def rootInBasis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (i j : Option (Fin n)) : Lattice n :=
  rootVertexInBasis b i - rootVertexInBasis b j

theorem rootInBasis_add (b : Module.Basis (Fin n) ℤ (Lattice n))
    (i j l : Option (Fin n)) :
    rootInBasis b i j + rootInBasis b j l = rootInBasis b i l := by
  unfold rootInBasis
  abel

/-- All roots of one integral basis, with both orientations and no extra rays. -/
def HasTypeARaysInBasis (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) : Prop :=
  ∀ u, u ∈ F.rays ↔ ∃ i j : Option (Fin n), i ≠ j ∧ u = rootInBasis b i j

def realCoordinates (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Ambient n →ₗ[ℝ] Ambient n :=
  (CoordinateQuotients.realBasis (FanBridge.standardEmbedding n)
    (FanBridge.standardEmbedding_isIntegralLattice n) b).equivFun.toLinearMap

lemma realCoordinates_embed (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n) :
    realCoordinates b (PaperVerification.ToricGeometry.embed n u) = fun i => (b.repr u i : ℝ) := by
  ext i
  change (CoordinateQuotients.realBasis (FanBridge.standardEmbedding n)
    (FanBridge.standardEmbedding_isIntegralLattice n) b).repr
      (FanBridge.standardEmbedding n u) i = _
  exact CoordinateQuotients.realBasis_repr _ _ b u i

lemma realCoordinates_vertex (b : Module.Basis (Fin n) ℤ (Lattice n))
    (i : Option (Fin n)) :
    realCoordinates b (PaperVerification.ToricGeometry.embed n (rootVertexInBasis b i)) = PaperVerification.ToricGeometry.embed n (rootVertex i) := by
  rw [realCoordinates_embed]
  cases i with
  | none =>
      ext j
      simp [rootVertexInBasis, rootVertex, PaperVerification.ToricGeometry.embed]
  | some i =>
      ext j
      simp [rootVertexInBasis, rootVertex, PaperVerification.ToricGeometry.embed,
        Module.Basis.repr_self_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]

lemma realCoordinates_root (b : Module.Basis (Fin n) ℤ (Lattice n))
    (i j : Option (Fin n)) :
    realCoordinates b (PaperVerification.ToricGeometry.embed n (rootInBasis b i j)) = PaperVerification.ToricGeometry.embed n (rootVector i j) := by
  simp only [rootInBasis, rootVector, map_sub, realCoordinates_vertex]

def cutInBasis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (S : Set (Option (Fin n))) : Ambient n →ₗ[ℝ] ℝ :=
  (cutLinear S).comp (realCoordinates b)

lemma cutInBasis_root (b : Module.Basis (Fin n) ℤ (Lattice n))
    (S : Set (Option (Fin n))) (i j : Option (Fin n)) :
    cutInBasis b S (PaperVerification.ToricGeometry.embed n (rootInBasis b i j)) =
      (if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then (1 : ℝ) else 0) := by
  simp only [cutInBasis, LinearMap.comp_apply, realCoordinates_root, cutLinear_root]

def coneSourcesInBasis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) : Set (Option (Fin n)) :=
  {i | ∃ j, i ≠ j ∧ rootInBasis b i j ∈ s}

variable (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

lemma no_two_edge_path_in_basis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hroots : HasTypeARaysInBasis F b) {s : Finset (Lattice n)} (hs : s ∈ F.cones)
    {i j l : Option (Fin n)} (hu : rootInBasis b i j ∈ s)
    (hv : rootInBasis b j l ∈ s) : False := by
  have h := sum_not_zero_or_ray F hs hu hv
  rw [rootInBasis_add] at h
  by_cases hil : i = l
  · subst l
    exact h.1 (sub_self _)
  · exact h.2 ((hroots _).mpr ⟨i, l, hil, rfl⟩)

/-- Convex unit-boundary support in every integral basis, on the same fan. -/
theorem unitBoundary_convexSupport_in_basis
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hroots : HasTypeARaysInBasis F b) :
    F.IsNef (fun _ => 1) := by
  intro s hs
  refine ⟨cutInBasis b (coneSourcesInBasis b s), ?_, ?_⟩
  · intro u hu
    obtain ⟨i, j, hij, rfl⟩ := (hroots u).mp (F.ray_mem_of_mem_cone hs hu)
    have hi : i ∈ coneSourcesInBasis b s := ⟨j, hij, hu⟩
    have hj : j ∉ coneSourcesInBasis b s := by
      rintro ⟨l, _, hl⟩
      exact no_two_edge_path_in_basis F b hroots hs hu hl
    simp only [cutInBasis_root, if_pos hi, if_neg hj, sub_zero]
  · intro u hu
    obtain ⟨i, j, _, rfl⟩ := (hroots u).mp hu
    rw [cutInBasis_root]
    split_ifs <;> norm_num

lemma rootInBasis_map (e : Lattice n ≃ₗ[ℤ] Lattice n) (i j : Option (Fin n)) :
    rootInBasis ((Pi.basisFun ℤ (Fin n)).map e) i j = e (rootVector i j) := by
  have hv (i : Option (Fin n)) :
      rootVertexInBasis ((Pi.basisFun ℤ (Fin n)).map e) i = e (rootVertex i) := by
    cases i <;> simp [rootVertexInBasis, rootVertex, Module.Basis.map_apply,
      Pi.basisFun_apply]
  simp only [rootInBasis, rootVector, map_sub, hv]

/-- Literal integral-isomorphism formulation of the ray hypothesis. -/
def HasTypeARaysUpToIntegralEquiv (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) : Prop :=
  ∃ e : Lattice n ≃ₗ[ℤ] Lattice n,
    ∀ u, u ∈ F.rays ↔ ∃ i j : Option (Fin n), i ≠ j ∧ u = e (rootVector i j)

theorem unitBoundary_convexSupport_of_integralEquiv
    (hroots : HasTypeARaysUpToIntegralEquiv F) : F.IsNef (fun _ => 1) := by
  obtain ⟨e, he⟩ := hroots
  apply unitBoundary_convexSupport_in_basis F ((Pi.basisFun ℤ (Fin n)).map e)
  intro u
  simpa only [rootInBasis_map] using he u

end Unimodular.TypeABoundary

namespace Unimodular.NefBig
open AlgebraicGeometry PaperVerification.ToricGeometry
universe u
variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- The nef-and-big conclusion for every fan integrally isomorphic on
its rays to the extremal type-A configuration. The scheme is unchanged. -/
theorem theorem_7_1_geometric_nef_and_big_of_integralEquiv
    (hroots : TypeABoundary.HasTypeARaysUpToIntegralEquiv F) :
    AlgebraicGeometry.IsNef (baseField := k) (anticanonicalLineBundle F k).obj ∧
      IsBig k (anticanonicalLineBundle F k).obj := by
  obtain ⟨hn, hb⟩ := anticanonical_nef_and_big_of_support F k
    (TypeABoundary.unitBoundary_convexSupport_of_integralEquiv F hroots)
  exact ⟨isNef_of_isNefOnCurves k _ hn, hb⟩

#print axioms theorem_7_1_geometric_nef_and_big_of_integralEquiv
end Unimodular.NefBig
