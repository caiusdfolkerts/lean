module
public import consolidated.actual_rigid_seeds

@[expose] public section

/-!
# Intrinsic rigid covers for the complete range of Lemma 14

Each covering piece below is rigid for its own induced geometric graph.
The theorem allows any graph whose edges on the selected vertex set are
actual polytope edges; it does not require every available edge to be used.

This supplements the relative `RigidInTail` covers used by the principal
theorem. The statements at the end specialize the result to the existing
`ParallelRigid` predicate without changing any checked release module.
-/

noncomputable section

namespace Papers.IntrinsicSmallOrderCovers

open Set Finset Papers.Polytopes Papers.ActualRigidity
open Papers.NeighborhoodCounts Papers.FiniteMatchingCovers
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators

variable {n : ℕ}

/-- Parallelism is imposed only on graph edges inside the indicated set. -/
def ParallelOnGraph (G : SimpleGraph (E n)) (A : Finset (E n))
    (f : E n → E n) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → EdgeParallel f x y

/-- Intrinsic parallel rigidity of a finite geometric subgraph. -/
def GraphRigid (G : SimpleGraph (E n)) (A : Finset (E n)) : Prop :=
  ∀ f : E n → E n, ParallelOnGraph G A f →
    ∃ a : ℝ, ∃ b : E n, ∀ x ∈ A, f x = a • x + b

/-- Ambient functions impose no extension restriction: this is equivalent
to quantifying over all maps defined on the literal vertex type of the piece. -/
theorem graphRigid_iff_vertex_domain (G : SimpleGraph (E n)) (A : Finset (E n)) :
    GraphRigid G A ↔
      ∀ f : A → E n,
        (∀ x y : A, G.Adj x.val y.val →
          ∃ μ : ℝ, f y - f x = μ • (y.val - x.val)) →
        ∃ a : ℝ, ∃ b : E n, ∀ x : A, f x = a • x.val + b := by
  constructor
  · intro h f hf
    let extended : E n → E n := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else 0
    have hp : ParallelOnGraph G A extended := by
      intro x hx y hy hxy
      simpa only [EdgeParallel, extended, dite_eq_left hx, dite_eq_left hy] using
        hf ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨a, b, hab⟩ := h extended hp
    refine ⟨a, b, ?_⟩
    intro x
    simpa only [extended, dite_eq_left x.property] using hab x.val x.property
  · intro h f hf
    obtain ⟨a, b, hab⟩ := h (fun x => f x.val)
      (fun x y hxy => hf x.val x.property y.val y.property hxy)
    exact ⟨a, b, fun x hx => hab ⟨x, hx⟩⟩

/-- Every graph edge under consideration is an actual edge of the polytope. -/
def EdgesAreActual (P : ConvexPolytope n) (G : SimpleGraph (E n))
    (T : Finset (E n)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, G.Adj x y → GeneralVertexStep P x y

/-- A cover by at most `m` intrinsically rigid induced subgraphs. -/
def HasIntrinsicGraphCover (G : SimpleGraph (E n)) (T : Finset (E n))
    (m : ℕ) : Prop :=
  ∃ C : Finset (Finset (E n)), C.card ≤ m ∧
    (∀ A ∈ C, A ⊆ T ∧ GraphRigid G A) ∧
    ∀ x ∈ T, ∃ A ∈ C, x ∈ A

theorem EdgesAreActual.mono {P : ConvexPolytope n} {G : SimpleGraph (E n)}
    {S T : Finset (E n)} (h : EdgesAreActual P G T) (hST : S ⊆ T) :
    EdgesAreActual P G S :=
  fun x hx y hy hxy => h x (hST hx) y (hST hy) hxy

theorem graphRigid_empty (G : SimpleGraph (E n)) : GraphRigid G ∅ := by
  intro f hf
  exact ⟨0, 0, by simp⟩

theorem graphRigid_pair (G : SimpleGraph (E n)) {u v : E n}
    (huv : G.Adj u v) : GraphRigid G {u, v} := by
  intro f hf
  obtain ⟨a, ha⟩ := hf u (by simp) v (by simp) huv
  refine ⟨a, f u - a • u, ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · module
  · have hxv := Finset.mem_singleton.mp hx
    subst x
    calc
      f v = (f v - f u) + f u := by abel
      _ = a • v + (f u - a • u) := by rw [ha]; module

theorem GraphRigid.insert_two_neighbors
    {P : ConvexPolytope n} {G : SimpleGraph (E n)} {T A : Finset (E n)}
    (hA : GraphRigid G A) (hTV : T ⊆ P.vertices) (hE : EdgesAreActual P G T)
    (hAT : A ⊆ T) {x u v : E n}
    (hx : x ∈ T) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) : GraphRigid G (insert x A) := by
  intro f hf
  obtain ⟨a, b, hab⟩ := hA f (fun y hy z hz hyz =>
    hf y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz) hyz)
  have hxval : f x = a • x + b :=
    absorb_actual_two_neighbors P ⟨x, hTV hx⟩ ⟨u, hTV (hAT hu)⟩
      ⟨v, hTV (hAT hv)⟩ (fun h => huv (congrArg Subtype.val h))
      (hE x hx u (hAT hu) hxu) (hE x hx v (hAT hv) hxv)
      f a b (hab u hu) (hab v hv)
      (hf x (by simp) u (Finset.mem_insert_of_mem hu) hxu)
      (hf x (by simp) v (Finset.mem_insert_of_mem hv) hxv)
  refine ⟨a, b, ?_⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hxval
  · exact hab z hz

theorem graphRigid_triangle (P : ConvexPolytope n) (G : SimpleGraph (E n))
    (T : Finset (E n)) (hTV : T ⊆ P.vertices) (hE : EdgesAreActual P G T)
    {u v w : E n} (hu : u ∈ T) (hv : v ∈ T) (hw : w ∈ T)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    GraphRigid G {u, v, w} := by
  intro f hf
  obtain ⟨a, b, hab⟩ := triangle_homothety P ⟨u, hTV hu⟩ ⟨v, hTV hv⟩
    ⟨w, hTV hw⟩ (hE u hu v hv huv) (hE u hu w hw huw) (hE v hv w hw hvw)
    f (hf u (by simp) v (by simp) huv) (hf u (by simp) w (by simp) huw)
    (hf v (by simp) w (by simp) hvw)
  exact ⟨a, b, fun x hx => hab x (by simpa using hx)⟩

structure LargestIntrinsicSet (G : SimpleGraph (E n))
    (T A : Finset (E n)) : Prop where
  subset : A ⊆ T
  rigid : GraphRigid G A
  largest : ∀ B ⊆ T, GraphRigid G B → B.card ≤ A.card

theorem exists_largest_intrinsic (G : SimpleGraph (E n)) (T : Finset (E n)) :
    ∃ A, LargestIntrinsicSet G T A := by
  let S := T.powerset.filter (GraphRigid G)
  have hS : S.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset T), graphRigid_empty G⟩⟩
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image S Finset.card hS
  obtain ⟨hAT, hAR⟩ := Finset.mem_filter.mp hA
  refine ⟨A, Finset.mem_powerset.mp hAT, hAR, ?_⟩
  intro B hBT hBR
  exact hmax B (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBT, hBR⟩)

theorem LargestIntrinsicSet.outside_degree_le_one
    {P : ConvexPolytope n} {G : SimpleGraph (E n)} {T A : Finset (E n)}
    (hA : LargestIntrinsicSet G T A) (hTV : T ⊆ P.vertices)
    (hE : EdgesAreActual P G T) {x : E n} (hx : x ∈ T) (hxA : x ∉ A) :
    (A.filter (G.Adj x)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huA, hxu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvA, hxv⟩ := Finset.mem_filter.mp hv
  by_contra huv
  have hnew := hA.rigid.insert_two_neighbors hTV hE hA.subset hx huA hvA huv hxu hxv
  have hle := hA.largest (insert x A) (Finset.insert_subset hx hA.subset) hnew
  rw [Finset.card_insert_of_notMem hxA] at hle
  omega

theorem LargestIntrinsicSet.residual_min_degree
    {P : ConvexPolytope n} {G : SimpleGraph (E n)} {T A : Finset (E n)}
    (hA : LargestIntrinsicSet G T A) (hTV : T ⊆ P.vertices)
    (hE : EdgesAreActual P G T) (k : ℕ)
    (hmin : ∀ x ∈ T, k + 1 ≤ (T.filter (G.Adj x)).card) :
    ∀ x ∈ T \ A, k ≤ ((T \ A).filter (G.Adj x)).card := by
  intro x hx
  obtain ⟨hxT, hxA⟩ := Finset.mem_sdiff.mp hx
  have hsmall := hA.outside_degree_le_one hTV hE hxT hxA
  have hlarge := hmin x hxT
  have hsub : A.filter (G.Adj x) ⊆ T.filter (G.Adj x) :=
    Finset.filter_subset_filter _ hA.subset
  have he : (T \ A).filter (G.Adj x) = T.filter (G.Adj x) \ A.filter (G.Adj x) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [he]
  omega

def inducedGraph (G : SimpleGraph (E n)) (T : Finset (E n)) : SimpleGraph T where
  Adj x y := G.Adj x.val y.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.ne rfl⟩

theorem inducedGraph_degree_eq (G : SimpleGraph (E n)) (T : Finset (E n)) (v : T) :
    (inducedGraph G T).degree v = (T.filter (G.Adj v.val)).card := by
  let e : (inducedGraph G T).neighborSet v ≃ T.filter (G.Adj v.val) := {
    toFun x := ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
    invFun x := ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
      (Finset.mem_filter.mp x.property).2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] using
    Fintype.card_congr e

/-- Absence of any intrinsic rigid set of size at least three rules out
three common neighbors. The entire five-vertex `K₂,₃` is retained. -/
theorem common_neighbors_le_two_of_no_intrinsic_three
    (P : ConvexPolytope n) (G : SimpleGraph (E n)) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (hE : EdgesAreActual P G T)
    (hno : ∀ A ⊆ T, 3 ≤ A.card → ¬ GraphRigid G A) :
    ∀ v w : T, w ∈ outsideStar (inducedGraph G T) v →
      localDegree (inducedGraph G T) ((inducedGraph G T).neighborFinset v) w ≤ 2 := by
  intro v w hw
  let H := inducedGraph G T
  have hwv : w ≠ v := by
    have h := (Finset.mem_sdiff.mp hw).2
    intro heq
    exact h (Finset.mem_insert.mpr (Or.inl heq))
  by_contra hlarge
  have hthree : 3 ≤ ((H.neighborFinset v).filter (H.Adj w)).card := by
    change ¬ ((H.neighborFinset v).filter (H.Adj w)).card ≤ 2 at hlarge
    omega
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hthree
  let e : Fin 3 ≃ S := (Fintype.equivFinOfCardEq (by simpa using hSc)).symm
  let a : Fin 3 → T := fun i => (e i).val
  let p : Fin 3 → P.vertices := fun i => ⟨(a i).val, hTV (a i).property⟩
  have ha : ∀ i, a i ∈ (H.neighborFinset v).filter (H.Adj w) :=
    fun i => hS (e i).property
  have hvg : ∀ i, G.Adj v.val (p i).val :=
    fun i => (H.mem_neighborFinset _ _).mp (Finset.mem_filter.mp (ha i)).1
  have hwg : ∀ i, G.Adj w.val (p i).val :=
    fun i => (Finset.mem_filter.mp (ha i)).2
  have hvE : ∀ i, GeneralVertexStep P v.val (p i).val :=
    fun i => hE v.val v.property (p i).val (a i).property (hvg i)
  have hwE : ∀ i, GeneralVertexStep P w.val (p i).val :=
    fun i => hE w.val w.property (p i).val (a i).property (hwg i)
  have hinj : Function.Injective p := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    change (p i).val = (p j).val
    exact congrArg Subtype.val hij
  have hinjval : Function.Injective (fun i => (p i).val) := by
    intro i j hij
    exact hinj (Subtype.ext hij)
  let B : Finset (E n) := Finset.univ.image (fun i => (p i).val)
  let A : Finset (E n) := insert v.val (insert w.val B)
  have hBc : B.card = 3 := by
    rw [Finset.card_image_of_injective _ hinjval]
    simp
  have hBA : B ⊆ A := by
    intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hAc : 3 ≤ A.card := by
    rw [← hBc]
    exact Finset.card_le_card hBA
  have hpA : ∀ i, (p i).val ∈ A := by
    intro i
    exact hBA (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hAT : A ⊆ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact v.property
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact w.property
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (a i).property
  apply hno A hAT hAc
  intro f hf
  obtain ⟨α, b, hhom⟩ := k23_homothety P ⟨v.val, hTV v.property⟩
    ⟨w.val, hTV w.property⟩ p
    (fun h => hwv (Subtype.ext (congrArg Subtype.val h).symm)) hinj hvE hwE f
    (fun i => hf v.val (by simp [A]) (p i).val (hpA i) (hvg i))
    (fun i => hf w.val (by simp [A]) (p i).val (hpA i) (hwg i))
  refine ⟨α, b, ?_⟩
  intro x hx
  apply hhom x
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Or.inl rfl
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Or.inr (Or.inl rfl)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Or.inr (Or.inr ⟨i, rfl⟩)

theorem exists_intrinsic_three_of_min_three
    (P : ConvexPolytope n) (G : SimpleGraph (E n)) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (hE : EdgesAreActual P G T)
    (hne : T.Nonempty) (hcard : T.card ≤ 7)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (G.Adj x)).card) :
    ∃ A ⊆ T, 3 ≤ A.card ∧ GraphRigid G A := by
  by_contra! hno
  let H := inducedGraph G T
  let : Nonempty T := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hHmin (v : T) : 3 ≤ H.degree v := by
    rw [inducedGraph_degree_eq]
    exact hmin v.val v.property
  have hcap := common_neighbors_le_two_of_no_intrinsic_three P G T hTV hE hno
  have hzero (v w : T) (hw : w ∈ H.neighborFinset v) :
      localDegree H (H.neighborFinset v) w = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huN, hwu⟩ := Finset.mem_filter.mp hu
    have hvw : G.Adj v.val w.val := (H.mem_neighborFinset _ _).mp hw
    have hvu : G.Adj v.val u.val := (H.mem_neighborFinset _ _).mp huN
    have hwu' : G.Adj w.val u.val := hwu
    let A : Finset (E n) := {v.val, w.val, u.val}
    have hAT : A ⊆ T := by
      intro x hx
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact Subtype.property _
    have hAc : A.card = 3 := by
      simp [A, hvw.ne, hvu.ne, hwu'.ne]
    exact hno A hAT (by omega)
      (graphRigid_triangle P G T hTV hE v.property w.property u.property hvw hvu hwu')
  have hreg (v : T) : H.degree v = 3 := by
    have hb := neighborhood_cut_bound H v 3 2 hHmin (hcap v)
    rw [outsideStar_card] at hb
    have hs : (∑ w ∈ H.neighborFinset v, localDegree H (H.neighborFinset v) w) = 0 :=
      Finset.sum_eq_zero (hzero v)
    rw [hs] at hb
    have hc : Fintype.card T ≤ 7 := by simpa only [Fintype.card_coe] using hcard
    have hd := hHmin v
    have hlt := H.degree_lt_card_verts v
    omega
  have hseven : Fintype.card T = 7 := by
    let v : T := Classical.choice inferInstance
    have hb := neighborhood_cut_bound H v 3 2 hHmin (hcap v)
    rw [outsideStar_card, hreg] at hb
    have hs : (∑ w ∈ H.neighborFinset v, localDegree H (H.neighborFinset v) w) = 0 :=
      Finset.sum_eq_zero (hzero v)
    rw [hs] at hb
    have hc : Fintype.card T ≤ 7 := by simpa only [Fintype.card_coe] using hcard
    omega
  have hparity := H.sum_degrees_eq_twice_card_edges
  simp only [hreg, Finset.sum_const, Finset.card_univ, hseven, smul_eq_mul] at hparity
  omega

theorem intrinsicGraphCover_empty (G : SimpleGraph (E n)) (m : ℕ) :
    HasIntrinsicGraphCover G ∅ m := by
  refine ⟨∅, by simp, ?_, ?_⟩ <;> simp

theorem HasIntrinsicGraphCover.mono {G : SimpleGraph (E n)} {T : Finset (E n)}
    {k m : ℕ} (h : HasIntrinsicGraphCover G T k) (hkm : k ≤ m) :
    HasIntrinsicGraphCover G T m := by
  obtain ⟨C, hC, hR, hcover⟩ := h
  exact ⟨C, hC.trans hkm, hR, hcover⟩

theorem intrinsicGraphCover_single {G : SimpleGraph (E n)} {T : Finset (E n)}
    (h : GraphRigid G T) : HasIntrinsicGraphCover G T 1 := by
  refine ⟨{T}, by simp, ?_, ?_⟩
  · intro A hA
    have he := Finset.mem_singleton.mp hA
    subst A
    exact ⟨Finset.Subset.refl _, h⟩
  · intro x hx
    exact ⟨T, Finset.mem_singleton_self _, hx⟩

theorem intrinsicGraphCover_pair {G : SimpleGraph (E n)} {T A B : Finset (E n)}
    (hAT : A ⊆ T) (hBT : B ⊆ T) (hAB : A ∪ B = T)
    (hA : GraphRigid G A) (hB : GraphRigid G B) : HasIntrinsicGraphCover G T 2 := by
  refine ⟨{A, B}, Finset.card_le_two, ?_, ?_⟩
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact ⟨hAT, hA⟩
    · exact ⟨hBT, hB⟩
  · intro x hx
    rw [← hAB] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨A, by simp, hx⟩
    · exact ⟨B, by simp, hx⟩

theorem HasIntrinsicGraphCover.adjoin {G : SimpleGraph (E n)}
    {T A : Finset (E n)} {m : ℕ}
    (h : HasIntrinsicGraphCover G (T \ A) m) (hAT : A ⊆ T) (hA : GraphRigid G A) :
    HasIntrinsicGraphCover G T (m + 1) := by
  obtain ⟨C, hC, hR, hcover⟩ := h
  refine ⟨insert A C,
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hC 1), ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨hAT, hA⟩
    · exact ⟨(hR B hB).1.trans Finset.sdiff_subset, (hR B hB).2⟩
  · intro x hx
    by_cases hxA : x ∈ A
    · exact ⟨A, Finset.mem_insert_self _ _, hxA⟩
    · obtain ⟨B, hB, hxB⟩ := hcover x (Finset.mem_sdiff.mpr ⟨hx, hxA⟩)
      exact ⟨B, Finset.mem_insert_of_mem hB, hxB⟩

theorem graphRigid_of_min_two_card_le_three
    (P : ConvexPolytope n) (G : SimpleGraph (E n)) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (_hE : EdgesAreActual P G T) (hcard : T.card ≤ 3)
    (hmin : ∀ x ∈ T, 2 ≤ (T.filter (G.Adj x)).card) : GraphRigid G T := by
  by_cases hne : T.Nonempty
  · have hcomplete {x y : E n} (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y) :
        G.Adj x y := by
      have hsub : T.filter (G.Adj x) ⊆ T.erase x := by
        intro z hz
        obtain ⟨hzT, hxz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_erase.mpr ⟨hxz.ne.symm, hzT⟩
      have he : T.filter (G.Adj x) = T.erase x := by
        apply Finset.eq_of_subset_of_card_le hsub
        rw [Finset.card_erase_of_mem hx]
        have hm := hmin x hx
        omega
      have hyf : y ∈ T.filter (G.Adj x) := by
        rw [he]
        exact Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
      exact (Finset.mem_filter.mp hyf).2
    obtain ⟨x, hx⟩ := hne
    have hm := hmin x hx
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (T.filter (G.Adj x)).card)
    obtain ⟨hyT, hxy⟩ := Finset.mem_filter.mp hy
    have hpairT : ({x, y} : Finset (E n)) ⊆ T := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    intro f hf
    obtain ⟨a, b, hab⟩ := graphRigid_pair G hxy f (fun u hu v hv huv =>
      hf u (hpairT hu) v (hpairT hv) huv)
    refine ⟨a, b, ?_⟩
    intro z hz
    by_cases hzx : z = x
    · subst z; exact hab x (by simp)
    by_cases hzy : z = y
    · subst z; exact hab y (by simp)
    have hxz := hcomplete hx hz (Ne.symm hzx)
    have hyz := hcomplete hyT hz (Ne.symm hzy)
    exact homothety_at_two_neighbors P f (hTV hx) (hTV hz) (hTV hyT)
      hxy.ne hzx hzy (hab x (by simp)) (hab y (by simp))
      (hf x hx z hz hxz) (hf y hyT z hz hyz)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact graphRigid_empty G

theorem intrinsicGraphCover_two_of_min_two_card_le_four
    (P : ConvexPolytope n) (G : SimpleGraph (E n)) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (hE : EdgesAreActual P G T) (hcard : T.card ≤ 4)
    (hmin : ∀ x ∈ T, 2 ≤ (T.filter (G.Adj x)).card) :
    HasIntrinsicGraphCover G T 2 := by
  by_cases hc3 : T.card ≤ 3
  · exact (intrinsicGraphCover_single
      (graphRigid_of_min_two_card_le_three P G T hTV hE hc3 hmin)).mono (by omega)
  have hc4 : T.card = 4 := by omega
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hT⟩ := Finset.card_eq_four.mp hc4
  have hdeg : ∀ x ∈ ({a, b, c, d} : Finset (E n)),
      2 ≤ (({a, b, c, d} : Finset (E n)).filter (G.Adj x)).card := by
    simpa only [hT] using hmin
  have hmatch := matching_cover_of_four_min_degree_two G a b c d
    hab hac had hbc hbd hcd hdeg
  have haT : a ∈ T := by simp [hT]
  have hbT : b ∈ T := by simp [hT]
  have hcT : c ∈ T := by simp [hT]
  have hdT : d ∈ T := by simp [hT]
  have cover (u v w z : E n) (hu : u ∈ T) (hv : v ∈ T) (hw : w ∈ T) (hz : z ∈ T)
      (he : ({u, v} : Finset (E n)) ∪ {w, z} = T)
      (huv : G.Adj u v) (hwz : G.Adj w z) : HasIntrinsicGraphCover G T 2 := by
    apply intrinsicGraphCover_pair (A := {u, v}) (B := {w, z})
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · exact he
    · exact graphRigid_pair G huv
    · exact graphRigid_pair G hwz
  rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply cover a b c d haT hbT hcT hdT _ h1 h2
    ext x
    simp only [hT, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · apply cover a c b d haT hcT hbT hdT _ h1 h2
    ext x
    simp only [hT, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · apply cover a d b c haT hdT hbT hcT _ h1 h2
    ext x
    simp only [hT, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Lemma 14 for an arbitrary actual-edge subgraph: seven vertices suffice
for a cover by three intrinsically rigid induced pieces. -/
theorem intrinsicGraphCover_three_of_min_three_card_le_seven
    (P : ConvexPolytope n) (G : SimpleGraph (E n)) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (hE : EdgesAreActual P G T) (hcard : T.card ≤ 7)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (G.Adj x)).card) :
    HasIntrinsicGraphCover G T 3 := by
  by_cases hne : T.Nonempty
  · obtain ⟨B, hBT, hBc, hBR⟩ :=
      exists_intrinsic_three_of_min_three P G T hTV hE hne hcard hmin
    obtain ⟨A, hA⟩ := exists_largest_intrinsic G T
    have hAc : 3 ≤ A.card := hBc.trans (hA.largest B hBT hBR)
    have hrem := Finset.card_sdiff_add_card_eq_card hA.subset
    have htail : (T \ A).card ≤ 4 := by omega
    have hdegree := hA.residual_min_degree hTV hE 2 hmin
    exact (intrinsicGraphCover_two_of_min_two_card_le_four P G (T \ A)
      (Finset.sdiff_subset.trans hTV) (hE.mono Finset.sdiff_subset) htail hdegree).adjoin
        hA.subset hA.rigid
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact intrinsicGraphCover_empty G 3

/-- The six-vertex range of Lemma 14: two intrinsically rigid pieces suffice. -/
theorem intrinsicGraphCover_two_of_min_three_card_le_six
    (P : ConvexPolytope n) (G : SimpleGraph (E n)) (T : Finset (E n))
    (hTV : T ⊆ P.vertices) (hE : EdgesAreActual P G T) (hcard : T.card ≤ 6)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (G.Adj x)).card) :
    HasIntrinsicGraphCover G T 2 := by
  by_cases hne : T.Nonempty
  · obtain ⟨B, hBT, hBc, hBR⟩ :=
      exists_intrinsic_three_of_min_three P G T hTV hE hne (by omega) hmin
    obtain ⟨A, hA⟩ := exists_largest_intrinsic G T
    have hAc : 3 ≤ A.card := hBc.trans (hA.largest B hBT hBR)
    have hrem := Finset.card_sdiff_add_card_eq_card hA.subset
    have htail : (T \ A).card ≤ 3 := by omega
    have hdegree := hA.residual_min_degree hTV hE 2 hmin
    exact (intrinsicGraphCover_single (graphRigid_of_min_two_card_le_three P G (T \ A)
      (Finset.sdiff_subset.trans hTV) (hE.mono Finset.sdiff_subset) htail hdegree)).adjoin
        hA.subset hA.rigid
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact intrinsicGraphCover_empty G 2

/-- The existing intrinsic polytope-edge predicate agrees with the graph
predicate on a set of actual vertices. -/
theorem graphRigid_actual_iff_parallelRigid (P : ConvexPolytope n)
    (A : Finset (E n)) (hA : A ⊆ P.vertices) :
    GraphRigid (Papers.PolytopeFourRegularTail.ambientActualGraph P) A ↔
      ParallelRigid P (A : Set (E n)) := by
  constructor
  · intro h f hf
    exact h f (fun x hx y hy hxy => hf x hx y hy hxy.2)
  · intro h f hf
    exact h f (fun x hx y hy hxy => hf x hx y hy ⟨hA hx, hxy⟩)

theorem actual_edges (P : ConvexPolytope n) (T : Finset (E n)) :
    EdgesAreActual P (Papers.PolytopeFourRegularTail.ambientActualGraph P) T :=
  fun _ _ _ _ h => h.2

theorem actual_neighbor_filter (P : ConvexPolytope n) (T : Finset (E n))
    {x : E n} (hx : x ∈ P.vertices) :
    T.filter ((Papers.PolytopeFourRegularTail.ambientActualGraph P).Adj x) =
      T.filter (GeneralVertexStep P x) := by
  apply Finset.filter_congr
  intro y _hy
  change (x ∈ P.vertices ∧ GeneralVertexStep P x y) ↔ GeneralVertexStep P x y
  exact ⟨And.right, fun h => ⟨hx, h⟩⟩

/-- The literal `ParallelRigid` formulation of the seven-vertex conclusion.
Every piece is independently rigid; no relative tail hypothesis occurs. -/
theorem intrinsicCover_three_of_min_three_card_le_seven
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hcard : T.card ≤ 7)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (GeneralVertexStep P x)).card) :
    ∃ C : Finset (Finset (E n)), C.card ≤ 3 ∧
      (∀ A ∈ C, A ⊆ T ∧ ParallelRigid P (A : Set (E n))) ∧
      ∀ x ∈ T, ∃ A ∈ C, x ∈ A := by
  obtain ⟨C, hC, hR, hcover⟩ := intrinsicGraphCover_three_of_min_three_card_le_seven P
    (Papers.PolytopeFourRegularTail.ambientActualGraph P) T hTV (actual_edges P T) hcard
    (by intro x hx; rw [actual_neighbor_filter P T (hTV hx)]; exact hmin x hx)
  exact ⟨C, hC, fun A hA => ⟨(hR A hA).1,
    (graphRigid_actual_iff_parallelRigid P A ((hR A hA).1.trans hTV)).mp (hR A hA).2⟩,
    hcover⟩

/-- The literal `ParallelRigid` formulation of the six-vertex conclusion. -/
theorem intrinsicCover_two_of_min_three_card_le_six
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (hcard : T.card ≤ 6)
    (hmin : ∀ x ∈ T, 3 ≤ (T.filter (GeneralVertexStep P x)).card) :
    ∃ C : Finset (Finset (E n)), C.card ≤ 2 ∧
      (∀ A ∈ C, A ⊆ T ∧ ParallelRigid P (A : Set (E n))) ∧
      ∀ x ∈ T, ∃ A ∈ C, x ∈ A := by
  obtain ⟨C, hC, hR, hcover⟩ := intrinsicGraphCover_two_of_min_three_card_le_six P
    (Papers.PolytopeFourRegularTail.ambientActualGraph P) T hTV (actual_edges P T) hcard
    (by intro x hx; rw [actual_neighbor_filter P T (hTV hx)]; exact hmin x hx)
  exact ⟨C, hC, fun A hA => ⟨(hR A hA).1,
    (graphRigid_actual_iff_parallelRigid P A ((hR A hA).1.trans hTV)).mp (hR A hA).2⟩,
    hcover⟩

end Papers.IntrinsicSmallOrderCovers

end
