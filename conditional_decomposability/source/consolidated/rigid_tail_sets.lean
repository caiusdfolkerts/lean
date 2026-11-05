module
public import consolidated.deletion_fields
public import consolidated.root_graph
public import consolidated_dev.intrinsic_figure_geometry
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option Elab.async false

section BundlePart0
/- Source: Papers/TailRigidityBasic.lean -/



@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {n : ℕ}
def ParallelOnTail (P : ConvexPolytope n) (T : Finset (E n)) (f : E n → E n) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, GeneralVertexStep P x y →
    ∃ μ : ℝ, f y - f x = μ • (y-x)
def RigidInTail (P : ConvexPolytope n) (T A : Finset (E n)) : Prop :=
  ∀ f : E n → E n, ParallelOnTail P T f →
    ∃ α : ℝ, ∃ b : E n, ∀ x ∈ A, f x = α • x + b
end Papers.PolytopeFourRegularTail


end
end
end BundlePart0

section BundlePart1
/- Source: Papers/ParallelRigidity.lean -/





@[expose] public section

/-!
# Local rigidity of the actual edge graph

The maps below are constrained only on edges with both endpoints in the
specified set. Thus the local rigidity claims quantify over every parallel
map of the induced geometric subgraph, not just maps that extend globally.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def IsParallelOn (P : ConvexPolytope d) (S : Set (E d)) (f : E d → E d) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GeneralVertexStep P x y →
    ∃ c : ℝ, f y - f x = c • (y - x)

def HomotheticOn (f : E d → E d) (S : Set (E d)) : Prop :=
  ∃ a : ℝ, ∃ b : E d, ∀ v ∈ S, f v = a • v + b

def ParallelRigid (P : ConvexPolytope d) (S : Set (E d)) : Prop :=
  ∀ f : E d → E d, IsParallelOn P S f → HomotheticOn f S

theorem IsParallelOn.mono {P : ConvexPolytope d} {S T : Set (E d)}
    {f : E d → E d} (hf : IsParallelOn P T f) (hST : S ⊆ T) :
    IsParallelOn P S f := by
  intro x hx y hy hxy
  exact hf x (hST hx) y (hST hy) hxy

theorem HomotheticOn.mono {S T : Set (E d)} {f : E d → E d}
    (hf : HomotheticOn f T) (hST : S ⊆ T) : HomotheticOn f S := by
  obtain ⟨a, b, hab⟩ := hf
  exact ⟨a, b, fun v hv => hab v (hST hv)⟩

theorem parallelOn_vertices_iff (P : ConvexPolytope d) (f : E d → E d) :
    IsParallelOn P (P.vertices : Set (E d)) f ↔ IsParallelMap P f := Iff.rfl

theorem homotheticOn_vertices_iff (P : ConvexPolytope d) (f : E d → E d) :
    HomotheticOn f (P.vertices : Set (E d)) ↔ IsHomothetyOnVertices P f := Iff.rfl

theorem affine_triple_coefficients {x y z : E d}
    (h : ¬Collinear ℝ ({x, y, z} : Set (E d))) {a b c : ℝ}
    (hsum : a + b + c = 0) (hlin : a • x + b • y + c • z = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hi : AffineIndependent ℝ ![x, y, z] :=
    affineIndependent_iff_not_collinear_set.mpr h
  have hz := hi.eq_zero_of_sum_eq_zero (s := Finset.univ) (w := ![a, b, c])
    (by simpa [Fin.sum_univ_succ, add_assoc] using hsum)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hlin)
  exact ⟨by simpa using hz 0 (Finset.mem_univ _),
    by simpa using hz 1 (Finset.mem_univ _),
    by simpa using hz 2 (Finset.mem_univ _)⟩

/-- An actual edge is rigid, including all possible scalar signs. -/
theorem parallelRigid_pair (P : ConvexPolytope d) {x y : E d}
    (hxy : GeneralVertexStep P x y) : ParallelRigid P ({x, y} : Set (E d)) := by
  intro f hf
  obtain ⟨a, ha⟩ := hf x (by simp) y (by simp) hxy
  refine ⟨a, f x - a • x, ?_⟩
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · abel
  · have h : v = y := Set.mem_singleton_iff.mp hv
    subst v
    calc
      f y = (f y - f x) + f x := by abel
      _ = _ := by rw [ha]; module

/-- Two neighbors already carrying a homothety force its value at a third
actual vertex. Noncollinearity is proved from extremality of the vertices. -/
theorem homothety_at_two_neighbors (P : ConvexPolytope d) (f : E d → E d)
    {u v w : E d} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (hw : w ∈ P.vertices) (huw : u ≠ w) (hvu : v ≠ u) (hvw : v ≠ w)
    {a : ℝ} {b : E d} (hfu : f u = a • u + b) (hfw : f w = a • w + b)
    (hvu' : ∃ c : ℝ, f v - f u = c • (v - u))
    (hvw' : ∃ c : ℝ, f v - f w = c • (v - w)) : f v = a • v + b := by
  obtain ⟨c, hc⟩ := hvu'
  obtain ⟨e, he⟩ := hvw'
  have hcu : f v = c • v + (a - c) • u + b := by
    calc
      f v = (f v - f u) + f u := by abel
      _ = c • (v - u) + (a • u + b) := by rw [hc, hfu]
      _ = _ := by module
  have hew : f v = e • v + (a - e) • w + b := by
    calc
      f v = (f v - f w) + f w := by abel
      _ = e • (v - w) + (a • w + b) := by rw [he, hfw]
      _ = _ := by module
  have hlin : (c - e) • v + (a - c) • u + (e - a) • w = 0 := by
    calc
      _ = (c • v + (a - c) • u + b) - (e • v + (a - e) • w + b) := by module
      _ = 0 := by rw [← hcu, ← hew, sub_self]
  have hzero := affine_triple_coefficients
    (vertices_not_collinear P hv hu hw hvu hvw huw) (by ring : c - e + (a - c) + (e - a) = 0)
    hlin
  have hac : a = c := sub_eq_zero.mp hzero.2.1
  simpa [← hac] using hcu

/-- A locally rigid set absorbs a vertex with two distinct neighbors in it. -/
theorem ParallelRigid.insert_two_neighbors {P : ConvexPolytope d} {S : Set (E d)}
    (hS : ParallelRigid P S) (hvertices : S ⊆ (P.vertices : Set (E d)))
    {v u w : E d} (hv : v ∈ P.vertices) (hu : u ∈ S) (hw : w ∈ S)
    (huw : u ≠ w) (huv : GeneralVertexStep P u v) (hwv : GeneralVertexStep P w v) :
    ParallelRigid P (insert v S) := by
  intro f hf
  obtain ⟨a, b, hab⟩ := hS f (hf.mono (Set.subset_insert v S))
  have hfv : f v = a • v + b :=
    homothety_at_two_neighbors P f (hvertices hu) hv (hvertices hw) huw
      huv.2.1.symm hwv.2.1.symm (hab u hu) (hab w hw)
      (hf u (Set.mem_insert_of_mem _ hu) v (Set.mem_insert _ _) huv)
      (hf w (Set.mem_insert_of_mem _ hw) v (Set.mem_insert _ _) hwv)
  refine ⟨a, b, ?_⟩
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact hfv
  · exact hab z hz

theorem parallelRigid_triangle (P : ConvexPolytope d) {u v w : E d}
    (hu : u ∈ P.vertices) (hv : v ∈ P.vertices) (hw : w ∈ P.vertices)
    (huv : GeneralVertexStep P u v) (huw : GeneralVertexStep P u w)
    (hvw : GeneralVertexStep P v w) : ParallelRigid P ({u, v, w} : Set (E d)) := by
  have hpair : ({u, v} : Set (E d)) ⊆ (P.vertices : Set (E d)) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  have h := (parallelRigid_pair P huv).insert_two_neighbors hpair hw
    (by simp : u ∈ ({u, v} : Set (E d))) (by simp : v ∈ ({u, v} : Set (E d)))
    huv.2.1 huw hvw
  convert h using 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem homothety_parameters_unique {u v : E d} (huv : u ≠ v)
    {a c : ℝ} {b e : E d}
    (hu : a • u + b = c • u + e) (hv : a • v + b = c • v + e) :
    a = c ∧ b = e := by
  have hz : (a - c) • (u - v) = 0 := by
    calc
      _ = ((a • u + b) - (c • u + e)) - ((a • v + b) - (c • v + e)) := by module
      _ = 0 := by rw [hu, hv]; abel
  have hac : a = c := sub_eq_zero.mp
    ((smul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr huv))
  refine ⟨hac, ?_⟩
  rw [hac] at hu
  exact add_left_cancel hu

/-- Two locally rigid subgraphs with two distinct common vertices merge. -/
theorem ParallelRigid.union_of_two_common {P : ConvexPolytope d} {S T : Set (E d)}
    (hS : ParallelRigid P S) (hT : ParallelRigid P T)
    {u v : E d} (huS : u ∈ S) (huT : u ∈ T) (hvS : v ∈ S) (hvT : v ∈ T)
    (huv : u ≠ v) : ParallelRigid P (S ∪ T) := by
  intro f hf
  obtain ⟨a, b, hab⟩ := hS f (hf.mono Set.subset_union_left)
  obtain ⟨c, e, hce⟩ := hT f (hf.mono Set.subset_union_right)
  obtain ⟨hac, hbe⟩ := homothety_parameters_unique huv
    ((hab u huS).symm.trans (hce u huT)) ((hab v hvS).symm.trans (hce v hvT))
  subst c
  subst e
  refine ⟨a, b, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · exact hab z hz
  · exact hce z hz

end Papers.Polytopes

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/RigidTailSets.lean -/





@[expose] public section

/-! Maximal rigid subsets of actual induced polytope graphs. -/

noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

theorem ParallelOnTail.mono {P : ConvexPolytope n} {T U : Finset (E n)}
    {f : E n → E n} (hf : ParallelOnTail P U f) (hTU : T ⊆ U) :
    ParallelOnTail P T f :=
  fun x hx y hy hxy => hf x (hTU hx) y (hTU hy) hxy

theorem RigidInTail.mono_target {P : ConvexPolytope n} {T A B : Finset (E n)}
    (h : RigidInTail P T B) (hAB : A ⊆ B) : RigidInTail P T A := by
  intro f hf
  obtain ⟨a,b,hab⟩ := h f hf
  exact ⟨a,b,fun x hx => hab x (hAB hx)⟩

theorem RigidInTail.mono_tail {P : ConvexPolytope n} {T U A : Finset (E n)}
    (h : RigidInTail P T A) (hTU : T ⊆ U) : RigidInTail P U A :=
  fun f hf => h f (hf.mono hTU)

theorem rigid_empty (P : ConvexPolytope n) (T : Finset (E n)) :
    RigidInTail P T ∅ := by
  intro f hf
  exact ⟨0,0,by simp⟩

theorem rigid_singleton (P : ConvexPolytope n) (T : Finset (E n)) (x : E n) :
    RigidInTail P T {x} := by
  intro f hf
  refine ⟨0,f x,?_⟩
  intro y hy
  have hyx := Finset.mem_singleton.mp hy
  subst y
  simp

theorem rigid_of_parallelRigid {P : ConvexPolytope n} {T A : Finset (E n)}
    (hAT : A ⊆ T) (hA : ParallelRigid P (A : Set (E n))) :
    RigidInTail P T A := by
  intro f hf
  exact hA f (hf.mono hAT)

theorem rigid_pair {P : ConvexPolytope n} {T : Finset (E n)}
    {x y : E n} (hx : x ∈ T) (hy : y ∈ T) (hxy : GeneralVertexStep P x y) :
    RigidInTail P T {x,y} := by
  apply rigid_of_parallelRigid
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using parallelRigid_pair P hxy

theorem rigid_triangle {P : ConvexPolytope n} {T : Finset (E n)}
    (hTV : T ⊆ P.vertices) {x y z : E n} (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T)
    (hxy : GeneralVertexStep P x y) (hxz : GeneralVertexStep P x z)
    (hyz : GeneralVertexStep P y z) : RigidInTail P T {x,y,z} := by
  apply rigid_of_parallelRigid
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using
      parallelRigid_triangle P (hTV hx) (hTV hy) (hTV hz) hxy hxz hyz

theorem RigidInTail.insert_two_neighbors
    {P : ConvexPolytope n} {T A : Finset (E n)} (hA : RigidInTail P T A)
    (hTV : T ⊆ P.vertices) (hAT : A ⊆ T) {x u v : E n}
    (hx : x ∈ T) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (hxu : GeneralVertexStep P x u) (hxv : GeneralVertexStep P x v) :
    RigidInTail P T (insert x A) := by
  intro f hf
  obtain ⟨a,b,hab⟩ := hA f hf
  have hxvalue : f x = a • x + b := by
    have huT := hAT hu
    have hvT := hAT hv
    have hux : GeneralVertexStep P u x :=
      ⟨hTV hx, hxu.2.1.symm, hxu.2.2.choose, hxu.2.2.choose_spec.1,
        hxu.2.2.choose_spec.2.1, hxu.2.2.choose_spec.2.2.2,
        hxu.2.2.choose_spec.2.2.1⟩
    have hvx : GeneralVertexStep P v x :=
      ⟨hTV hx, hxv.2.1.symm, hxv.2.2.choose, hxv.2.2.choose_spec.1,
        hxv.2.2.choose_spec.2.1, hxv.2.2.choose_spec.2.2.2,
        hxv.2.2.choose_spec.2.2.1⟩
    exact homothety_at_two_neighbors P f (hTV huT) (hTV hx) (hTV hvT) huv
      hxu.2.1 hxv.2.1 (hab u hu) (hab v hv)
      (hf u huT x hx hux) (hf v hvT x hx hvx)
  refine ⟨a,b,?_⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hxvalue
  · exact hab z hz

structure LargestRigidSet (P : ConvexPolytope n) (T A : Finset (E n)) : Prop where
  subset : A ⊆ T
  rigid : RigidInTail P T A
  largest : ∀ B ⊆ T, RigidInTail P T B → B.card ≤ A.card

theorem exists_largest_rigid (P : ConvexPolytope n) (T : Finset (E n)) :
    ∃ A, LargestRigidSet P T A := by
  let S := T.powerset.filter (RigidInTail P T)
  have hS : S.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset T), rigid_empty P T⟩⟩
  obtain ⟨A,hA,hmax⟩ := Finset.exists_max_image S Finset.card hS
  obtain ⟨hAT,hAR⟩ := Finset.mem_filter.mp hA
  refine ⟨A, Finset.mem_powerset.mp hAT, hAR, ?_⟩
  intro B hBT hBR
  exact hmax B (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBT,hBR⟩)

theorem LargestRigidSet.outside_degree_le_one
    {P : ConvexPolytope n} {T A : Finset (E n)} (hA : LargestRigidSet P T A)
    (hTV : T ⊆ P.vertices) {x : E n} (hx : x ∈ T) (hxA : x ∉ A) :
    (A.filter (fun u => GeneralVertexStep P x u)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huA,hxu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvA,hxv⟩ := Finset.mem_filter.mp hv
  by_contra huv
  have hnew := hA.rigid.insert_two_neighbors hTV hA.subset hx huA hvA huv hxu hxv
  have hle := hA.largest (insert x A) (Finset.insert_subset hx hA.subset) hnew
  rw [Finset.card_insert_of_notMem hxA] at hle
  omega

theorem LargestRigidSet.residual_min_degree
    {P : ConvexPolytope n} {T A : Finset (E n)} (hA : LargestRigidSet P T A)
    (hTV : T ⊆ P.vertices) (k : ℕ)
    (hmin : ∀ x ∈ T, k+1 ≤ (T.filter (fun u => GeneralVertexStep P x u)).card) :
    ∀ x ∈ T \ A, k ≤ ((T \ A).filter (fun u => GeneralVertexStep P x u)).card := by
  intro x hx
  obtain ⟨hxT,hxA⟩ := Finset.mem_sdiff.mp hx
  have hsmall := hA.outside_degree_le_one hTV hxT hxA
  have hlarge := hmin x hxT
  have hsub : A.filter (fun u => GeneralVertexStep P x u) ⊆
      T.filter (fun u => GeneralVertexStep P x u) := Finset.filter_subset_filter _ hA.subset
  have he : (T \ A).filter (fun u => GeneralVertexStep P x u) =
      (T.filter (fun u => GeneralVertexStep P x u)) \
        (A.filter (fun u => GeneralVertexStep P x u)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [he]
  omega

end Papers.PolytopeFourRegularTail

end
end
end BundlePart2

