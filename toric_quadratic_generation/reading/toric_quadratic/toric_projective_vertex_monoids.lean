module

public import PaperVerification.ToricHomogeneousMonoidCharts
public import PaperVerification.ToricPointedMonoids
public import PaperVerification.ToricVertexCone
public import PaperVerification.ToricStatements
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Pointedness of actual monomial vertex charts

At an actual vertex of the convex hull of the weights, strict separation
gives a nonnegative functional on all weight differences, vanishing only
at zero. Additive closure preserves this property, so the corresponding
actual affine Proj chart has a pointed exponent monoid.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open PaperVerification.ToricGeometry PaperVerification.ToricVertexCone
open scoped Classical

theorem nonnegative_strict_on_closure {M : Type*} [AddCommGroup M]
    (S : Set M) (f : M →+ ℝ)
    (hS : ∀ x∈S,0≤f x ∧ (f x=0 → x=0)) :
    ∀ x∈AddSubmonoid.closure S,0≤f x ∧ (f x=0 → x=0) := by
  intro x hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      refine ⟨add_nonneg ihx.1 ihy.1,?_⟩
      intro h
      have hx0 : f x=0 := by linarith [ihy.1]
      have hy0 : f y=0 := by linarith [ihx.1]
      rw [ihx.2 hx0,ihy.2 hy0,zero_add]

theorem pointed_closure_of_positive_functional {M : Type*} [AddCommGroup M]
    (S : Set M) (f : M →+ ℝ)
    (hS : ∀ x∈S,0≤f x ∧ (f x=0 → x=0)) :
    IsPointedMonoid (AddSubmonoid.closure S) := by
  intro x hx y hy hxy
  have hx' := nonnegative_strict_on_closure S f hS x hx
  have hy' := nonnegative_strict_on_closure S f hS y hy
  have he : f x+f y=0 := by rw [← map_add,hxy,map_zero]
  exact ⟨hx'.2 (by linarith),hy'.2 (by linarith)⟩

/-- Every actual vertex weight gives a pointed difference semigroup,
including a one-point hull in dimension zero or in a proper subspace. -/
theorem differenceWeightMonoid_pointed_at_vertex {ι : Type*} [Fintype ι]
    {n : ℕ} (a : ι → Lattice n) (j : ι)
    (hj : embed n (a j)∈
      (convexHull ℝ (Set.range (fun i=>embed n (a i)))).extremePoints ℝ) :
    IsPointedMonoid (differenceWeightMonoid a j) := by
  let s : Finset (Ambient n) := Finset.univ.image (fun i=>embed n (a i))
  have hj' : embed n (a j)∈(convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa [s] using hj
  obtain ⟨h,hh⟩ := exists_strict_vertex_functional s hj'
  let f : Lattice n →+ ℝ := h.toLinearMap.toAddMonoidHom.comp (embed n)
  apply pointed_closure_of_positive_functional _ f
  rintro x ⟨i,rfl⟩
  by_cases he : a i=a j
  · simp [he,f]
  · have her : embed n (a i)≠embed n (a j) := (embed_injective n).ne he
    have hpos : 0<f (a i-a j) := by
      simpa [f,map_sub] using hh (embed n (a i))
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) her
    exact ⟨hpos.le,fun hz=>(hpos.ne' hz).elim⟩

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.differenceWeightMonoid_pointed_at_vertex
