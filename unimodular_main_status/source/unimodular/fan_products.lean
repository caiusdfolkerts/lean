module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# Complete fans on a direct sum of ray configurations

The geometric part of Proposition 4.1 of *Unimodular configurations and complete fans*.
All cones below are actual Mathlib pointed cones. The ambient fan is Tau Ceti's finite,
lattice-rational, salient fan, with its usual face and intersection axioms. The index set is
an arbitrary finite type; no simpliciality, unimodularity or projectivity is required.
-/

open scoped BigOperators

namespace Unimodular.FanProducts

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]

/-- The actual Cartesian product of a family of cones. -/
def conePi (C : ∀ j, PointedCone ℝ (V j)) : PointedCone ℝ (∀ j, V j) :=
  Submodule.pi Set.univ C

@[simp] theorem mem_conePi (C : ∀ j, PointedCone ℝ (V j)) (x : ∀ j, V j) :
    x ∈ conePi C ↔ ∀ j, x j ∈ C j := by
  simp [conePi, Submodule.mem_pi]

/-- The intersection of a cone with a coordinate summand, expressed in that summand. -/
def sectionCone (C : PointedCone ℝ (∀ j, V j)) (j : J) : PointedCone ℝ (V j) :=
  C.comap (LinearMap.single ℝ V j)

@[simp] theorem mem_sectionCone (C : PointedCone ℝ (∀ j, V j)) (j : J) (x : V j) :
    x ∈ sectionCone C j ↔ Pi.single j x ∈ C := Iff.rfl

/-- Coordinate projections of a member remain in the cone. This will be derived from the
actual extremal-ray condition, rather than assumed in the main theorem. -/
def Splits (C : PointedCone ℝ (∀ j, V j)) : Prop :=
  ∀ x ∈ C, ∀ j, Pi.single j (x j) ∈ C

theorem single_injective (j : J) : Function.Injective (LinearMap.single ℝ V j) := by
  intro x y h
  have := congrFun h j
  simpa using this

@[simp] theorem sectionCone_map_single (C : PointedCone ℝ (V j)) :
    sectionCone (C.map (LinearMap.single ℝ V j)) j = C := by
  ext x
  simp only [mem_sectionCone, PointedCone.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    exact (single_injective j h) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem Splits.eq_conePi {C : PointedCone ℝ (∀ j, V j)} (hC : Splits C) :
    C = conePi (sectionCone C) := by
  ext x
  constructor
  · intro hx
    exact (mem_conePi _ _).2 fun j => hC x hx j
  · intro hx
    rw [← LinearMap.sum_single_apply V x]
    exact C.sum_mem fun j _ => (mem_conePi _ _).1 hx j

theorem Splits.section_eq_map {C : PointedCone ℝ (∀ j, V j)} (hC : Splits C) (j : J) :
    sectionCone C j = C.map (LinearMap.proj j) := by
  ext x
  constructor
  · intro hx
    exact ⟨Pi.single j x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact hC y hy j

theorem sectionCone_salient {C : PointedCone ℝ (∀ j, V j)}
    (hC : (C : ConvexCone ℝ (∀ j, V j)).Salient) (j : J) :
    (sectionCone C j : ConvexCone ℝ (V j)).Salient := by
  intro x hx hx0 hnx
  apply hC (Pi.single j x) hx
  · intro h
    apply hx0
    have := congrFun h j
    simpa using this
  · change Pi.single j (-x) ∈ C at hnx
    change -(Pi.single j x) ∈ C
    simpa only [Pi.single_neg] using hnx

/-- Each coordinate section is a face of a salient cone which splits. -/
theorem Splits.map_section_isFaceOf {C : PointedCone ℝ (∀ j, V j)}
    (hC : Splits C) (hsal : (C : ConvexCone ℝ (∀ j, V j)).Salient) (j : J) :
    ((sectionCone C j).map (LinearMap.single ℝ V j)).IsFaceOf C := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro x y hx hy hxy
    obtain ⟨z, hz, heq⟩ := hxy
    have hxzero : ∀ k, k ≠ j → x k = 0 := by
      intro k hkj
      have hk : x k + y k = 0 := by
        have := congrFun heq k
        simpa [Pi.single_eq_of_ne hkj] using this.symm
      by_contra hne
      apply hsal (Pi.single k (x k)) (hC x hx k)
      · intro h
        apply hne
        have := congrFun h k
        simpa using this
      · have hyk := hC y hy k
        have hneg : y k = -x k := eq_neg_of_add_eq_zero_right hk
        change -(Pi.single k (x k)) ∈ C
        simpa only [hneg, Pi.single_neg] using hyk
    have he : Pi.single j (x j) = x := by
      ext k
      by_cases hk : k = j
      · subst k
        simp
      · simp [Pi.single_eq_of_ne hk, hxzero k hk]
    exact ⟨x j, hC x hx j, he⟩

theorem conePi_isFaceOf {C F : ∀ j, PointedCone ℝ (V j)}
    (h : ∀ j, (F j).IsFaceOf (C j)) : (conePi F).IsFaceOf (conePi C) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (mem_conePi _ _).2 fun j => (h j).le ((mem_conePi _ _).1 hx j)
  · intro x y a hx hy ha hxy
    exact (mem_conePi _ _).2 fun j => (h j).mem_of_smul_add_mem
      ((mem_conePi _ _).1 hx j) ((mem_conePi _ _).1 hy j) ha
      ((mem_conePi _ _).1 hxy j)

/-- The ray condition in Proposition 4.1: each actual extremal ray is contained in one
coordinate summand. Opposite rays are distinct cones and are retained. -/
def RaysInSummands (C : PointedCone ℝ (∀ j, V j)) : Prop :=
  ∀ ρ : TauCeti.Toric.ToricRay C, ∃ j,
    ∀ x ∈ ρ.toPointedCone, ∀ k, k ≠ j → x k = 0

theorem splits_of_raysInSummands {C : PointedCone ℝ (∀ j, V j)}
    (hfg : C.FG) (hsal : (C : ConvexCone ℝ (∀ j, V j)).Salient)
    (h : RaysInSummands C) : Splits C := by
  intro x hx j
  have hle : C ≤ C.comap ((LinearMap.single ℝ V j).comp (LinearMap.proj j)) := by
    apply (TauCeti.Toric.ToricRay.iSup_toPointedCone hfg hsal).ge.trans
    refine iSup_le fun ρ => ?_
    intro y hy
    obtain ⟨k, hk⟩ := h ρ
    change Pi.single j (y j) ∈ C
    by_cases hjk : j = k
    · subst j
      have he : Pi.single k (y k) = y := by
        ext l
        by_cases hl : l = k
        · subst l
          simp
        · simp [Pi.single_eq_of_ne hl, hk y hy l hl]
      rw [he]
      exact ρ.1.isFaceOf.le hy
    · rw [hk y hy j hjk, Pi.single_zero]
      exact C.zero_mem
  exact hle hx

/-- A point whose smallest face is the whole finitely generated cone. Using a finite
generating sum avoids any choice of coordinates or relative-interior convention. -/
theorem exists_face_detecting_point {W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : PointedCone ℝ W) (hfg : C.FG) :
    ∃ x ∈ C, ∀ F : PointedCone ℝ W, F.IsFaceOf C → x ∈ F → C ≤ F := by
  classical
  obtain ⟨s, hs⟩ := hfg
  refine ⟨∑ v ∈ s, v, C.sum_mem (fun v hv => hs ▸ PointedCone.subset_hull hv), ?_⟩
  intro F hF hx
  rw [← hs]
  apply Submodule.span_le.2
  intro v hv
  have hx' : ∑ w : s, (w : W) ∈ F := by
    rwa [Finset.sum_coe_sort s (fun w : W => w)]
  exact hF.mem_of_sum_mem (fun w => hs ▸ PointedCone.subset_hull w.2) hx' ⟨v, hv⟩

end Unimodular.FanProducts
