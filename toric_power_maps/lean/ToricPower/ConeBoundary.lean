module

public import ToricPower.ConePyramid
public import ToricPower.RationalConeInequalities
public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp

/-!
# Integral interior points and radial boundary decomposition

An integral point in no proper face is obtained by summing finite
integral generators. For any nonzero point of a rational salient cone,
the minimum positive halfspace ratio moves every other point to a
proper supporting face. These statements also cover cones of less than
full dimension.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped BigOperators Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {C F : PointedCone ℝ V}

/-- A literal integral point that determines the entire face. -/
theorem rationalCone_exists_integral_interior (rational : IsLatticeRational i C) :
    ∃ q : N, i q ∈ C ∧
      ∀ F : PointedCone ℝ V, F.IsFaceOf C → i q ∈ F → C ≤ F := by
  classical
  obtain ⟨s, spans⟩ := isLatticeRational_iff.mp rational
  let q : N := ∑ n : s, (n : N)
  have value : i q = ∑ n : s, i n := map_sum i _ _
  have generatorMember (n : s) : i n ∈ C := by
    rw [spans]
    exact PointedCone.subset_hull (Set.mem_image_of_mem i n.property)
  refine ⟨q, ?_, ?_⟩
  · rw [value]
    exact C.sum_mem fun n _ => generatorMember n
  · intro F face member
    rw [spans]
    apply Submodule.span_le.mpr
    rintro _ ⟨n, hn, rfl⟩
    rw [value] at member
    exact face.mem_of_sum_mem generatorMember member ⟨n, hn⟩

theorem rationalCone_exists_nonzero_integral_interior (toric : IsToricCone i C)
    (nonzero : C ≠ ⊥) :
    ∃ q : N, i q ∈ C ∧ i q ≠ 0 ∧
      ∀ F : PointedCone ℝ V, F.IsFaceOf C → i q ∈ F → C ≤ F := by
  obtain ⟨q, member, determines⟩ := rationalCone_exists_integral_interior toric.rational
  refine ⟨q, member, ?_, determines⟩
  intro zero
  apply nonzero
  apply le_antisymm _ bot_le
  apply determines ⊥ toric.salient.bot_isFaceOf
  rw [zero]
  exact Submodule.zero_mem _

/-- Moving along the negative radial direction reaches a proper face.
The face does not contain the radial point, even when that point itself
lies on some other boundary face. -/
theorem rationalCone_boundary_decomposition (lattice : IsIntegralLattice i)
    (toric : IsToricCone i C) {p x : V} (hp : p ∈ C) (hpzero : p ≠ 0) (hx : x ∈ C) :
    ∃ (F : PointedCone ℝ V), F.IsFaceOf C ∧ p ∉ F ∧ x ∈ rayJoin p F := by
  classical
  obtain ⟨s, membership⟩ := rationalCone_exists_integral_inequalities lattice C toric.rational
  let positive := s.filter fun m => 0 < lattice.realCharacter m p
  have positiveNonempty : positive.Nonempty := by
    by_contra hempty
    have nonpositive (m : N →+ ℤ) (hm : m ∈ s) : lattice.realCharacter m p ≤ 0 := by
      apply le_of_not_gt
      intro h
      exact hempty ⟨m, Finset.mem_filter.mpr ⟨hm, h⟩⟩
    have negMember : -p ∈ C := (membership (-p)).mpr fun m hm => by
      rw [map_neg]
      exact neg_nonneg.mpr (nonpositive m hm)
    exact toric.salient p hp hpzero negMember
  obtain ⟨m, hm, minimal⟩ := positive.exists_min_image
    (fun m => lattice.realCharacter m x / lattice.realCharacter m p) positiveNonempty
  have member : m ∈ s := (Finset.mem_filter.mp hm).1
  have denominator : 0 < lattice.realCharacter m p := (Finset.mem_filter.mp hm).2
  let a : ℝ := lattice.realCharacter m x / lattice.realCharacter m p
  have aNonnegative : 0 ≤ a := div_nonneg ((membership x).mp hx m member) denominator.le
  let y : V := x - a • p
  have yMember : y ∈ C := by
    apply (membership y).mpr
    intro k hk
    have kpNonnegative := (membership p).mp hp k hk
    have kxNonnegative := (membership x).mp hx k hk
    change 0 ≤ lattice.realCharacter k (x - a • p)
    rw [map_sub, map_smul, smul_eq_mul]
    by_cases kpzero : lattice.realCharacter k p = 0
    · simpa only [kpzero, mul_zero, sub_zero] using kxNonnegative
    · have kpPositive : 0 < lattice.realCharacter k p :=
        lt_of_le_of_ne kpNonnegative (Ne.symm kpzero)
      have bound : a ≤ lattice.realCharacter k x / lattice.realCharacter k p :=
        minimal k (Finset.mem_filter.mpr ⟨hk, kpPositive⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ kpPositive).mp bound)
  let F := C ⊓ PointedCone.ofSubmodule (LinearMap.ker (lattice.realCharacter m))
  have face : F.IsFaceOf C := PointedCone.isFaceOf_inf_ker
    (fun z hz => (membership z).mp hz m member)
  have yFace : y ∈ F := by
    refine ⟨yMember, ?_⟩
    change lattice.realCharacter m (x - a • p) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    dsimp [a]
    rw [div_mul_cancel₀ _ denominator.ne', sub_self]
  refine ⟨F, face, ?_, ?_⟩
  · intro pFace
    have zero : lattice.realCharacter m p = 0 := pFace.2
    exact denominator.ne' zero
  · exact mem_rayJoin.mpr ⟨a, aNonnegative, y, yFace, by dsimp [y]; abel⟩

/-- A proper face has strictly smaller real span. -/
theorem face_span_lt (face : F.IsFaceOf C) (proper : F ≠ C) :
    Submodule.span ℝ (F : Set V) < Submodule.span ℝ (C : Set V) := by
  refine lt_of_le_of_ne (Submodule.span_mono face.le) ?_
  intro equality
  apply proper
  apply le_antisymm face.le
  intro x hx
  apply face_mem_of_mem_span face hx
  rw [equality]
  exact Submodule.subset_span hx

theorem face_finrank_lt [FiniteDimensional ℝ V]
    (face : F.IsFaceOf C) (proper : F ≠ C) :
    Module.finrank ℝ (Submodule.span ℝ (F : Set V)) <
      Module.finrank ℝ (Submodule.span ℝ (C : Set V)) :=
  Submodule.finrank_lt_finrank_of_lt (face_span_lt face proper)

end ToricPower.FanSubdivision
end
