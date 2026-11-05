module

public import Recovery.Unimodular.WeakFano.EffectiveDirection
public import Unimodular.FanOrientations

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Set

namespace Unimodular.EffectiveMatrixGeometry

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def center (u : E → Lattice n) : Lattice n := ∑ e, u e

def sign (z : ℤ) : ℤ := if 0 < z then 1 else if z < 0 then -1 else 0

/-- Finite cofactor candidates; no facet orientation is supplied as input. -/
def normalTest (u : E → Lattice n) (s : Finset E) (p : (Fin n → E) × Fin n) : Prop :=
  Matrix.det (u ∘ p.1) ≠ 0 ∧ ∀ e ∈ s, EffectiveDirection.rowForm (u ∘ p.1) p.2 (u e) = 0

instance (u : E → Lattice n) (s : Finset E) (p : (Fin n → E) × Fin n) :
    Decidable (normalTest u s p) := by unfold normalTest; infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The sum of all generators is an actual interior point of every
full-dimensional finitely generated cone, including nonsimplicial cones. -/
theorem center_interior (u : E → Lattice n)
    (hfull : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤) :
    embed (center u) ∈ interior
      (PointedCone.hull ℝ (Set.range (fun e => embed (u e))) : Set (Ambient n)) := by
  let C := PointedCone.hull ℝ (Set.range (fun e => embed (u e)))
  let x : Ambient n := ∑ e, embed (u e)
  have hx : x ∈ C := C.sum_mem fun e _ => PointedCone.subset_hull ⟨e, rfl⟩
  have hF := MinimalFaces.dominatedCone_isFaceOf C x
  have hFx := MinimalFaces.self_mem_dominatedCone hx
  have hgen : ∀ e, embed (u e) ∈ MinimalFaces.dominatedCone C x :=
    hF.mem_of_sum_mem (fun e => PointedCone.subset_hull ⟨e, rfl⟩) hFx
  have heq : MinimalFaces.dominatedCone C x = C := by
    apply le_antisymm hF.le
    apply Submodule.span_le.2
    rintro y ⟨e, rfl⟩
    exact hgen e
  have hspan : Submodule.span ℝ (C : Set (Ambient n)) = ⊤ := by
    rw [RayHyperplanes.span_hull_eq]
    exact hfull
  have hi := (ConeInterior.mem_interior_iff_dominatedCone_eq
    (ConeInterior.interior_nonempty_of_span_eq_top hspan) hx).2 heq
  have hsum : embed (center u) = x := by
    ext i
    simp [center, x, embed, Finset.sum_apply]
  simpa only [hsum] using hi

/-- Nonzero determinant gives a genuinely nonzero real cofactor functional. -/
theorem realRowForm_ne_zero (a : Fin n → Lattice n) (i : Fin n)
    (ha : Matrix.det a ≠ 0) : EffectiveDirection.realRowForm a i ≠ 0 := by
  intro h
  have he := congrArg (fun f : Ambient n →ₗ[ℝ] ℝ => f (embed (a i))) h
  rw [EffectiveDirection.realRowForm_embed, LinearMap.zero_apply,
    EffectiveDirection.rowForm_apply, Function.update_eq_self] at he
  exact ha (by exact_mod_cast he)

/-- Every accepted cofactor is an actual normal to the entire original
codimension-one ray span. -/
theorem normalTest_kernel (u : E → Lattice n) (s : Finset E)
    (hs : Module.finrank ℝ (RayHyperplanes.raySpan (fun e => embed (u e)) s) + 1 = n)
    (p : (Fin n → E) × Fin n) (hp : normalTest u s p) :
    LinearMap.ker (EffectiveDirection.realRowForm (u ∘ p.1) p.2) =
      RayHyperplanes.raySpan (fun e => embed (u e)) s := by
  have hne := realRowForm_ne_zero (u ∘ p.1) p.2 hp.1
  have hle : RayHyperplanes.raySpan (fun e => embed (u e)) s ≤
      LinearMap.ker (EffectiveDirection.realRowForm (u ∘ p.1) p.2) := by
    apply Submodule.span_le.2
    rintro x ⟨e, he, rfl⟩
    change EffectiveDirection.realRowForm (u ∘ p.1) p.2 (embed (u e)) = 0
    rw [EffectiveDirection.realRowForm_embed, hp.2 e he, Int.cast_zero]
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  have hn : Module.finrank ℝ (Ambient n) = n := by simp [Ambient]
  rw [hn] at hd
  omega

/-- The complete finite row-candidate family contains an orientation for
every actual codimension-one block. No selected normal is assumed. -/
theorem exists_normalTest (u : E → Lattice n)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (s : Finset E)
    (hs : Module.finrank ℝ (RayHyperplanes.raySpan (fun e => embed (u e)) s) + 1 = n) :
    ∃ p : (Fin n → E) × Fin n, normalTest u s p := by
  have hproper : RayHyperplanes.raySpan (fun e => embed (u e)) s ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hs
    have hn : Module.finrank ℝ (Ambient n) = n := by simp [Ambient]
    rw [hn] at hs
    omega
  obtain ⟨a, i, ha, hker⟩ := EffectiveDirection.exists_tuple_and_missing_row u hspan s hproper
  refine ⟨(a, i), ha, ?_⟩
  intro e he
  have hh := hker (Submodule.subset_span (show embed (u e) ∈
    (fun e => embed (u e)) '' (s : Set E) from ⟨e, he, rfl⟩))
  change EffectiveDirection.realRowForm (u ∘ a) i (embed (u e)) = 0 at hh
  rw [EffectiveDirection.realRowForm_embed] at hh
  exact_mod_cast hh

theorem sign_cast (z : ℤ) : FacetLine.signZ (z : ℝ) = sign z := by
  simp only [FacetLine.signZ, sign, Int.cast_pos, Int.cast_lt_zero]

/-- An actual supporting normal has the same sign at every pair of
interior points; this makes a computable generator sum interchangeable
with the original definition's abstract interior point. -/
theorem sign_eq_on_interior {C F : PointedCone ℝ (Ambient n)}
    (hF : F.IsFaceOf C) (hne : F ≠ C) (f : Ambient n →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker f = Submodule.span ℝ (F : Set (Ambient n)))
    {x y : Ambient n} (hx : x ∈ interior (C : Set (Ambient n)))
    (hy : y ∈ interior (C : Set (Ambient n))) :
    FacetLine.signZ (f x) = FacetLine.signZ (f y) := by
  have hfx := ConeInterior.normal_ne_zero_at_interior hF hne f hker hx
  have hfy := ConeInterior.normal_ne_zero_at_interior hF hne f hker hy
  rcases lt_or_gt_of_ne hfx with hneg | hpos
  · have hyn : f y < 0 := by
      by_contra h
      have hyp : 0 < f y := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hfy)
      have hxn := ConeInterior.normal_nonneg_on_cone hF f hker (interior_subset hy) hyp
        x (interior_subset hx)
      linarith
    rw [FacetLine.signZ_of_neg hneg, FacetLine.signZ_of_neg hyn]
  · have hyn := ConeInterior.normal_nonneg_on_cone hF f hker (interior_subset hx) hpos
      y (interior_subset hy)
    have hyp : 0 < f y := lt_of_le_of_ne hyn (Ne.symm hfy)
    rw [FacetLine.signZ_of_pos hpos, FacetLine.signZ_of_pos hyp]

end
end Unimodular.EffectiveMatrixGeometry

#print axioms Unimodular.EffectiveMatrixGeometry.center_interior
#print axioms Unimodular.EffectiveMatrixGeometry.normalTest_kernel
#print axioms Unimodular.EffectiveMatrixGeometry.exists_normalTest
#print axioms Unimodular.EffectiveMatrixGeometry.sign_eq_on_interior
#check Unimodular.EffectiveMatrixGeometry.exists_normalTest
