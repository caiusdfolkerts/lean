module

public import dirichlet_strong

/-!
# Maximum principles on an enclosed finite vertex region

These lemmas do not assume that a region is itself triangulated. Its graph
boundary consists exactly of the exterior neighbours of its vertices. The
geometric Jordan-curve argument supplies that boundary and an actual escaping
path. This avoids silently using a topological subtriangulation theorem.
-/

@[expose] public section

namespace NormalProjective.Dirichlet

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def vertexFrontier (G : SimpleGraph V) (S : Set V) : Set V :=
  {v | v ∉ S ∧ ∃ u ∈ S, G.Adj u v}

theorem neighbor_eq_of_neighbor_max (G : SimpleGraph V) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ G.Adj i j → w i j = 0)
    (x : V → ℝ) {i j : V} (hi : Harmonic w x i)
    (hmax : ∀ k, G.Adj i k → x k ≤ x i) (hij : G.Adj i j) :
    x j = x i := by
  have hnonneg : ∀ k ∈ (univ : Finset V), 0 ≤ w i k * (x i - x k) := by
    intro k _
    by_cases hik : G.Adj i k
    · exact mul_nonneg (hw i k) (sub_nonneg.mpr (hmax k hik))
    · simp [hoff i k hik]
  have hz : w i j * (x i - x j) = 0 :=
    (sum_eq_zero_iff_of_nonneg hnonneg).mp hi j (mem_univ j)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (ne_of_gt (he i j hij)))).symm

/-- The weak maximum principle for any proper finite vertex region. No
connectedness of the region itself is required. -/
theorem maximum_on_region (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (hproper : ∃ b, b ∉ S) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ G.Adj i j → w i j = 0)
    (x : V → ℝ) (hx : ∀ i ∈ S, Harmonic w x i)
    (c : ℝ) (hbd : ∀ i ∈ vertexFrontier G S, x i ≤ c) :
    ∀ i ∈ S, x i ≤ c := by
  classical
  intro i hi
  by_contra hci
  have hci : c < x i := lt_of_not_ge hci
  let A : Finset V := univ.filter (· ∈ S)
  obtain ⟨u,hu,hmax⟩ := exists_max_image A x ⟨i,by simp [A,hi]⟩
  have huS : u ∈ S := (mem_filter.mp hu).2
  have hmaxS : ∀ v ∈ S, x v ≤ x u := fun v hv => hmax v (by simp [A,hv])
  have hcu : c < x u := hci.trans_le (hmaxS i hi)
  have hstep : ∀ v z, G.Adj v z → (v ∈ S ∧ x v = x u) →
      z ∈ S ∧ x z = x u := by
    intro v z hvz hv
    have hnb : ∀ k, G.Adj v k → x k ≤ x v := by
      intro k hvk
      rw [hv.2]
      by_cases hk : k ∈ S
      · exact hmaxS k hk
      · exact (hbd k ⟨hk,v,hv.1,hvk⟩).trans hcu.le
    have heq : x z = x u :=
      (neighbor_eq_of_neighbor_max G w hw he hoff x (hx v hv.1) hnb hvz).trans hv.2
    refine ⟨?_,heq⟩
    by_contra hz
    exact not_lt_of_ge (hbd z ⟨hz,v,hv.1,hvz⟩) (heq ▸ hcu)
  have hwalk : ∀ {v z}, G.Walk v z → (v ∈ S ∧ x v = x u) →
      z ∈ S ∧ x z = x u := by
    intro v z p
    induction p with
    | nil => exact id
    | @cons v z t hvz p ih => exact fun hv => ih (hstep v z hvz hv)
  obtain ⟨b,hb⟩ := hproper
  obtain ⟨p⟩ := hG u b
  exact hb (hwalk p ⟨huS,rfl⟩).1

/-- A strict boundary barrier along an actual path gives strictness at its
starting interior vertex. The path may leave the region; its first exit is
forced to have the same value by harmonicity, contradicting the strict barrier.
The subset `A` is used to avoid finitely many exceptional zero-valued vertices. -/
theorem strict_maximum_on_region_along_path (G : SimpleGraph V) (hG : G.Connected)
    (S A : Set V) (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (he : ∀ i j, G.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ G.Adj i j → w i j = 0)
    (x : V → ℝ) (hx : ∀ i ∈ S, Harmonic w x i)
    (c : ℝ) (hbd : ∀ i ∈ vertexFrontier G S, x i ≤ c)
    (hstrict : ∀ i ∈ A, i ∈ vertexFrontier G S → x i < c)
    (i b : V) (hiS : i ∈ S) (hiA : i ∈ A) (hbS : b ∉ S) (hbA : b ∈ A)
    (hpath : (G.induce A).Reachable ⟨i,hiA⟩ ⟨b,hbA⟩) : x i < c := by
  have hweak := maximum_on_region G hG S ⟨b,hbS⟩ w hw he hoff x hx c hbd
  by_contra hnot
  have hic : x i = c := le_antisymm (hweak i hiS) (le_of_not_gt hnot)
  have hstep : ∀ (v z : A), (G.induce A).Adj v z →
      ((v : V) ∈ S ∧ x v = c) → (z : V) ∈ S ∧ x z = c := by
    intro v z hvz hv
    have hnb : ∀ k, G.Adj v k → x k ≤ x v := by
      intro k hvk
      rw [hv.2]
      by_cases hk : k ∈ S
      · exact hweak k hk
      · exact hbd k ⟨hk,v,hv.1,hvk⟩
    have heq : x z = c :=
      (neighbor_eq_of_neighbor_max G w hw he hoff x (hx v hv.1) hnb hvz).trans hv.2
    refine ⟨?_,heq⟩
    by_contra hz
    exact (hstrict z z.property ⟨hz,v,hv.1,hvz⟩).ne heq
  have hwalk : ∀ {v z : A}, (G.induce A).Walk v z →
      ((v : V) ∈ S ∧ x v = c) → (z : V) ∈ S ∧ x z = c := by
    intro v z p
    induction p with
    | nil => exact id
    | @cons v z t hvz p ih => exact fun hv => ih (hstep v z hvz hv)
  obtain ⟨p⟩ := hpath
  exact hbS (hwalk p ⟨hiS,hic⟩).1

end NormalProjective.Dirichlet
