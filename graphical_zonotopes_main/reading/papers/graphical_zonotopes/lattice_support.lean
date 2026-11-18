module

public import Papers.GraphicalZonotopes.Lattice
public import Mathlib.Data.Finset.Max

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem LatticePolytope.compact {Q : Set (V → ℝ)} (hQ : LatticePolytope Q) : IsCompact Q := by
  obtain ⟨P,rfl⟩ := hQ
  exact (P.finite_toSet.image _).isCompact_convexHull ℝ

theorem LatticePolytope.convex {Q : Set (V → ℝ)} (hQ : LatticePolytope Q) : Convex ℝ Q := by
  obtain ⟨P,rfl⟩ := hQ
  exact convex_convexHull ℝ _

/-- Integer lower-support values follow from a genuine lattice convex-hull
presentation; the converse direction of the lattice correspondence is explicit. -/
theorem LatticePolytope.lowerSupport_integerValued {Q : Set (V → ℝ)}
    (hQ : LatticePolytope Q) (hne : Q.Nonempty) : IntegerValued (lowerSupport Q) := by
  classical
  obtain ⟨P,rfl⟩ := hQ
  have hP : P.Nonempty := by
    by_contra h
    have hE : P = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [hE] at hne
  intro S
  let vals : Finset ℤ := P.image (fun x => ∑ v ∈ S, x v)
  have hvals : vals.Nonempty := hP.image _
  let a : ℤ := vals.min' hvals
  have hamem : a ∈ vals := min'_mem _ _
  obtain ⟨p,hp,hpa⟩ := mem_image.mp hamem
  have hmin : ∀ q ∈ P, a ≤ ∑ v ∈ S, q v := by
    intro q hq
    exact min'_le vals _ (mem_image.mpr ⟨q,hq,rfl⟩)
  have hconv : Convex ℝ {x : V → ℝ | (a : ℝ) ≤ subsetSum x S} := by
    intro x hx y hy r s hr hs hrs
    change (a : ℝ) ≤ subsetSum (r • x+s • y) S
    rw [subsetSum_add,subsetSum_smul,subsetSum_smul]
    have h1 := mul_le_mul_of_nonneg_left hx hr
    have h2 := mul_le_mul_of_nonneg_left hy hs
    calc
      (a : ℝ) = r*(a : ℝ)+s*(a : ℝ) := by rw [← add_mul,hrs,one_mul]
      _ ≤ r*subsetSum x S+s*subsetSum y S := add_le_add h1 h2
  have hbound : convexHull ℝ
      ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ))) ⊆
      {x : V → ℝ | (a : ℝ) ≤ subsetSum x S} := by
    apply convexHull_min _ hconv
    rintro x ⟨q,hq,rfl⟩
    change (a : ℝ) ≤ ∑ v ∈ S, (q v : ℝ)
    exact_mod_cast hmin q hq
  have hpQ : (fun v => (p v : ℝ)) ∈ convexHull ℝ
      ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ))) :=
    subset_convexHull ℝ _ ⟨p,hp,rfl⟩
  have hsum : subsetSum (fun v => (p v : ℝ)) S = (a : ℝ) := by
    change (∑ v ∈ S, (p v : ℝ)) = (a : ℝ)
    exact_mod_cast hpa
  have hleast : IsLeast ((fun x => subsetSum x S) '' convexHull ℝ
      ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ)))) (a : ℝ) := by
    refine ⟨⟨_,hpQ,hsum⟩,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact hbound hx
  exact ⟨a,hleast.csInf_eq⟩

theorem IntegerValued.delta {z : SetFunction V} (hz : IntegerValued z)
    (u v : V) (S : Finset V) : ∃ a : ℤ, GraphicalZonotopes.delta z u v S = (a : ℝ) := by
  obtain ⟨a,ha⟩ := hz (insert u (insert v S))
  obtain ⟨b,hb⟩ := hz (insert u S)
  obtain ⟨c,hc⟩ := hz (insert v S)
  obtain ⟨d,hd⟩ := hz S
  exact ⟨a-b-c+d,by simp [GraphicalZonotopes.delta,ha,hb,hc,hd]⟩

theorem IntegerValued.positive_delta_ge_one {z : SetFunction V} (hz : IntegerValued z)
    (u v : V) (S : Finset V) (hp : 0 < GraphicalZonotopes.delta z u v S) : 1 ≤ GraphicalZonotopes.delta z u v S := by
  obtain ⟨a,ha⟩ := hz.delta u v S
  rw [ha] at hp ⊢
  have hi : 0 < a := by exact_mod_cast hp
  exact_mod_cast (show 1 ≤ a by omega)

theorem IntegerValued.modular (t : V → ℝ) (ht : ∀ v, ∃ a : ℤ, t v = (a : ℝ)) :
    IntegerValued (GraphicalZonotopes.modular t) := by
  classical
  choose a ha using ht
  intro S
  refine ⟨∑ v ∈ S, a v,?_⟩
  simp [GraphicalZonotopes.modular,subsetSum,ha]

theorem IntegerValued.normalize {z : SetFunction V} (hz : IntegerValued z) :
    IntegerValued (GraphicalZonotopes.normalize z) :=
  hz.sub (IntegerValued.modular (fun v => z {v}) (fun v => hz {v}))

end GraphicalZonotopes
