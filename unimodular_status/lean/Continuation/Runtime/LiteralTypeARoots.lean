module

public import Continuation.Runtime.HellerRootLattice
public import Continuation.Divisor.TypeAIntegralCoordinates

/-!
# The literal type-A lattice and the original fan's anticanonical bundle

The Heller equality theorem uses the actual kernel of the sum map on
`ℤ^(n+1)`.  The support-function proof uses differences of the vertices
`0, e₁, …, eₙ` in `ℤ^n`.  This file proves their exact equivalence, in
both directions, before applying the latter theorem to the original fan.
No fan is replaced, and no projectivity hypothesis is introduced.

This is a proof-source candidate until its exact compiler receipt exists.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Unimodular.TypeABoundary

open PaperVerification.ToricGeometry

variable {n : ℕ}

/-- The two rooted-incidence conventions use exactly the same lattice vectors. -/
theorem rootVertex_eq_graphicVertex (p : Option (Fin n)) :
    rootVertex p = Graphic.vertex (Pi.basisFun ℤ (Fin n)) p := by
  cases p with
  | none => rfl
  | some i => simp [rootVertex, Graphic.vertex, Pi.basisFun_apply]

/-- The explicit zero-sum coordinates carry every directed root to the
paper's literal `eᵢ - eⱼ`, with its orientation unchanged. -/
theorem coordinateEquiv_rootVector (p q : Option (Fin n)) :
    Heller.TypeA.coordinateEquiv n (rootVector p q) =
      Heller.TypeA.root (Heller.TypeA.vertexIndex p) (Heller.TypeA.vertexIndex q) := by
  simpa only [rootVector, rootVertex_eq_graphicVertex] using
    Heller.TypeA.coordinateEquiv_difference p q

/-- Exact set equality, retaining all and only unequal ordered endpoint pairs. -/
theorem coordinateEquiv_image_rootVectors :
    Heller.TypeA.coordinateEquiv n ''
      {u : Lattice n | ∃ p q : Option (Fin n), p ≠ q ∧ u = rootVector p q} =
        Heller.TypeA.roots n := by
  ext u
  constructor
  · rintro ⟨v, ⟨p, q, hpq, rfl⟩, rfl⟩
    exact ⟨Heller.TypeA.vertexIndex p, Heller.TypeA.vertexIndex q,
      fun h => hpq (Heller.TypeA.vertexIndex_bijective.1 h),
      coordinateEquiv_rootVector p q⟩
  · rintro ⟨i, j, hij, rfl⟩
    obtain ⟨p, rfl⟩ := Heller.TypeA.vertexIndex_bijective.2 i
    obtain ⟨q, rfl⟩ := Heller.TypeA.vertexIndex_bijective.2 j
    refine ⟨rootVector p q, ⟨p, q, ?_, rfl⟩, coordinateEquiv_rootVector p q⟩
    exact fun h => hij (congrArg Heller.TypeA.vertexIndex h)

/-- An integral identification with the literal zero-sum root set is
equivalent to the exact coordinate hypothesis used by the support proof.
The statement is about arbitrary sets, so it requires neither a chosen
enumeration nor a cardinality or spanning assumption. -/
theorem integral_root_set_iff (S : Set (Lattice n)) :
    (∃ φ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
      φ '' S = Heller.TypeA.roots n) ↔
    ∃ e : Lattice n ≃ₗ[ℤ] Lattice n,
      ∀ u, u ∈ S ↔ ∃ p q : Option (Fin n), p ≠ q ∧ u = e (rootVector p q) := by
  constructor
  · rintro ⟨φ, hφ⟩
    let e : Lattice n ≃ₗ[ℤ] Lattice n :=
      (Heller.TypeA.coordinateEquiv n).trans φ.symm
    refine ⟨e, fun u => ?_⟩
    constructor
    · intro hu
      have hm : φ u ∈ Heller.TypeA.roots n := hφ ▸ ⟨u, hu, rfl⟩
      rw [← coordinateEquiv_image_rootVectors] at hm
      obtain ⟨v, ⟨p, q, hpq, rfl⟩, hv⟩ := hm
      refine ⟨p, q, hpq, ?_⟩
      apply φ.injective
      simpa only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hv.symm
    · rintro ⟨p, q, hpq, rfl⟩
      have hr : Heller.TypeA.coordinateEquiv n (rootVector p q) ∈
          Heller.TypeA.roots n := by
        rw [← coordinateEquiv_image_rootVectors]
        exact ⟨rootVector p q, ⟨p, q, hpq, rfl⟩, rfl⟩
      have hm : φ (e (rootVector p q)) ∈ φ '' S := by
        rw [hφ]
        simpa only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hr
      obtain ⟨v, hv, he⟩ := hm
      exact φ.injective he ▸ hv
  · rintro ⟨e, he⟩
    refine ⟨e.symm.trans (Heller.TypeA.coordinateEquiv n), ?_⟩
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨p, q, hpq, rfl⟩ := (he v).mp hv
      change Heller.TypeA.coordinateEquiv n (e.symm (e (rootVector p q))) ∈ _
      rw [e.symm_apply_apply, ← coordinateEquiv_image_rootVectors]
      exact ⟨rootVector p q, ⟨p, q, hpq, rfl⟩, rfl⟩
    · intro hu
      rw [← coordinateEquiv_image_rootVectors] at hu
      obtain ⟨v, ⟨p, q, hpq, rfl⟩, rfl⟩ := hu
      refine ⟨e (rootVector p q), (he _).mpr ⟨p, q, hpq, rfl⟩, ?_⟩
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The Heller equality conclusion is precisely the hypothesis of the
nef-and-big theorem, on the unchanged original smooth complete fan. -/
theorem hasTypeARaysUpToIntegralEquiv_iff_literal
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) :
    HasTypeARaysUpToIntegralEquiv F ↔
      ∃ φ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
        φ '' (F.rays : Set (Lattice n)) = Heller.TypeA.roots n :=
  (integral_root_set_iff (F.rays : Set (Lattice n))).symm

end Unimodular.TypeABoundary

namespace Unimodular.NefBig

open AlgebraicGeometry PaperVerification.ToricGeometry

universe u
variable {n : ℕ}

/-- The geometric clause of Theorem 7.1 with its literal root-lattice
hypothesis. This concerns the original scheme and its intrinsic
anticanonical line bundle, including nonprojective fans and rank zero. -/
theorem theorem_7_1_nef_and_big_of_literal_roots
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) (k : Type u) [Field k]
    (hroots : ∃ φ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
      φ '' (F.rays : Set (Lattice n)) = Heller.TypeA.roots n) :
    AlgebraicGeometry.IsNef (baseField := k) (anticanonicalLineBundle F k).obj ∧
      IsBig k (anticanonicalLineBundle F k).obj :=
  theorem_7_1_geometric_nef_and_big_of_integralEquiv F k
    ((TypeABoundary.hasTypeARaysUpToIntegralEquiv_iff_literal F).mpr hroots)

#print axioms TypeABoundary.coordinateEquiv_rootVector
#print axioms TypeABoundary.coordinateEquiv_image_rootVectors
#print axioms TypeABoundary.integral_root_set_iff
#print axioms TypeABoundary.hasTypeARaysUpToIntegralEquiv_iff_literal
#print axioms theorem_7_1_nef_and_big_of_literal_roots

end Unimodular.NefBig
