module

public import Papers.GraphicalZonotopes.PathSupport
public import Papers.GraphicalZonotopes.Lattice

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

theorem window_eq_iff {n i j : ℕ} {T U : Finset ℕ} (hT0 : 0 ∈ T) (hU0 : 0 ∈ U)
    (hT : ∀ k ∈ T, i + k < n) (hU : ∀ k ∈ U, j + k < n) :
    window n i T = window n j U ↔ i = j ∧ T = U := by
  have hi : i < n := by simpa using hT 0 hT0
  have hj : j < n := by simpa using hU 0 hU0
  constructor
  · intro he
    have hiM : (⟨i, hi⟩ : Fin n) ∈ window n i T := by simp [hT0]
    have hjM : (⟨j, hj⟩ : Fin n) ∈ window n j U := by simp [hU0]
    rw [he] at hiM
    rw [← he] at hjM
    have hij : i = j := le_antisymm ((mem_window n i T _).mp hjM).1
      ((mem_window n j U _).mp hiM).1
    refine ⟨hij, ?_⟩
    subst j
    ext k
    constructor
    · intro hk
      have hkM : (⟨i+k, hT k hk⟩ : Fin n) ∈ window n i T := by simp [hk]
      rw [he] at hkM
      simpa using ((mem_window n i U _).mp hkM).2
    · intro hk
      have hkM : (⟨i+k, hU k hk⟩ : Fin n) ∈ window n i U := by simp [hk]
      rw [← he] at hkM
      simpa using ((mem_window n i T _).mp hkM).2
  · rintro ⟨rfl, rfl⟩
    rfl

theorem window_clique {n i : ℕ} {T : Finset ℕ} (hT : T ⊆ {0,1,2,3}) :
    ∀ u ∈ window n i T, ∀ v ∈ window n i T, u ≠ v → (graph n).Adj u v := by
  intro u hu v hv huv
  obtain ⟨hu0, huT⟩ := (mem_window n i T u).mp hu
  obtain ⟨hv0, hvT⟩ := (mem_window n i T v).mp hv
  have h1 := hT huT
  have h2 := hT hvT
  simp only [mem_insert, mem_singleton] at h1 h2
  exact ⟨huv, by omega, by omega⟩

def coefficients (n : ℕ) : SetFunction (Fin n) :=
  (∑ i : Fin (n-2), Pi.single (window n i.val {0,1,2}) 1) +
  (∑ i : Fin (n-3), Pi.single (window n i.val {0,2,3}) 1) -
  (∑ i : Fin (n-3), Pi.single (window n i.val {0,1,2,3}) 1)

def setFunction (n : ℕ) : SetFunction (Fin n) := zeta (coefficients n)

theorem sum_single_window {n N i : ℕ} {T U : Finset ℕ}
    (hT0 : 0 ∈ T) (hU0 : 0 ∈ U)
    (hT : ∀ k ∈ T, i+k < n) (hU : ∀ j : Fin N, ∀ k ∈ U, j.val+k < n) :
    (∑ j : Fin N, (Pi.single (window n j.val U) (1 : ℝ) : SetFunction (Fin n))) (window n i T) =
      if T = U then (if i < N then 1 else 0) else 0 := by
  classical
  simp only [Finset.sum_apply, Pi.single_apply]
  have he : ∀ j : Fin N, window n i T = window n j.val U ↔ i = j.val ∧ T = U :=
    fun j => window_eq_iff hT0 hU0 hT (hU j)
  simp_rw [he]
  by_cases hTU : T = U
  · simp only [hTU, and_true, if_true]
    by_cases hi : i < N
    · rw [if_pos hi]
      rw [sum_eq_single (⟨i, hi⟩ : Fin N)]
      · simp
      · intro j hj hji
        have hval : i ≠ j.val := by intro hv; apply hji; exact Fin.ext hv.symm
        simp [hval]
      · simp
    · rw [if_neg hi]
      apply sum_eq_zero
      intro j hj
      have hval : i ≠ j.val := by intro h; rw [h] at hi; exact hi j.isLt
      simp [hval]
  · simp [hTU]

theorem coefficients_window {n i : ℕ} {T : Finset ℕ} (hT0 : 0 ∈ T)
    (hT : ∀ k ∈ T, i+k < n) :
    coefficients n (window n i T) =
      (if T = {0,1,2} then (if i < n-2 then 1 else 0) else 0) +
      (if T = {0,2,3} then (if i < n-3 then 1 else 0) else 0) -
      (if T = {0,1,2,3} then (if i < n-3 then 1 else 0) else 0) := by
  unfold coefficients
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [sum_single_window hT0 (by simp) hT (by
    intro j k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
  rw [sum_single_window hT0 (by simp) hT (by
    intro j k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
  rw [sum_single_window hT0 (by simp) hT (by
    intro j k hk; simp only [mem_insert, mem_singleton] at hk; omega)]

theorem coordinates_coefficients (n : ℕ) : coordinates (coefficients n) = scale n 1 := by
  have hm01 : ({0,1} : Finset ℕ) ≠ {0,2} := by decide
  have hm10 := Ne.symm hm01
  have hm02 : ({0,1} : Finset ℕ) ≠ {0,3} := by decide
  have hm20 := Ne.symm hm02
  have hm03 : ({0,1} : Finset ℕ) ≠ {0,1,2} := by decide
  have hm30 := Ne.symm hm03
  have hm04 : ({0,1} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm40 := Ne.symm hm04
  have hm05 : ({0,1} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm50 := Ne.symm hm05
  have hm06 : ({0,1} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm60 := Ne.symm hm06
  have hm12 : ({0,2} : Finset ℕ) ≠ {0,3} := by decide
  have hm21 := Ne.symm hm12
  have hm13 : ({0,2} : Finset ℕ) ≠ {0,1,2} := by decide
  have hm31 := Ne.symm hm13
  have hm14 : ({0,2} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm41 := Ne.symm hm14
  have hm15 : ({0,2} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm51 := Ne.symm hm15
  have hm16 : ({0,2} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm61 := Ne.symm hm16
  have hm23 : ({0,3} : Finset ℕ) ≠ {0,1,2} := by decide
  have hm32 := Ne.symm hm23
  have hm24 : ({0,3} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm42 := Ne.symm hm24
  have hm25 : ({0,3} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm52 := Ne.symm hm25
  have hm26 : ({0,3} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm62 := Ne.symm hm26
  have hm34 : ({0,1,2} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm43 := Ne.symm hm34
  have hm35 : ({0,1,2} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm53 := Ne.symm hm35
  have hm36 : ({0,1,2} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm63 := Ne.symm hm36
  have hm45 : ({0,1,3} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm54 := Ne.symm hm45
  have hm46 : ({0,1,3} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm64 := Ne.symm hm46
  have hm56 : ({0,2,3} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm65 := Ne.symm hm56
  apply Coordinates.ext <;> funext i <;> dsimp [coordinates]
  all_goals
    rw [coefficients_window (by simp) (by
      intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num [scale, i.isLt,hm01,hm10,hm02,hm20,hm03,hm30,hm04,hm40,hm05,hm50,hm06,hm60,hm12,hm21,hm13,hm31,hm14,hm41,hm15,hm51,hm16,hm61,hm23,hm32,hm24,hm42,hm25,hm52,hm26,hm62,hm34,hm43,hm35,hm53,hm36,hm63,hm45,hm54,hm46,hm64,hm56,hm65]

theorem coefficients_supported (n : ℕ) : CliqueSupported (graph n) (coefficients n) := by
  have hzero : ∀ C : Finset (Fin n),
      (∀ i : Fin (n-2), window n i.val {0,1,2} ≠ C) →
      (∀ i : Fin (n-3), window n i.val {0,2,3} ≠ C) →
      (∀ i : Fin (n-3), window n i.val {0,1,2,3} ≠ C) → coefficients n C = 0 := by
    intro C h1 h2 h3
    simp [coefficients, Pi.single_apply, h1, h2, h3]
  have hc012 : ∀ i : Fin (n-2), (window n i.val {0,1,2}).card = 3 := by
    intro i
    rw [window_card _ (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num
  have hc023 : ∀ i : Fin (n-3), (window n i.val {0,2,3}).card = 3 := by
    intro i
    rw [window_card _ (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num
  have hc0123 : ∀ i : Fin (n-3), (window n i.val {0,1,2,3}).card = 4 := by
    intro i
    rw [window_card _ (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · apply hzero
    · intro i h; have hh := hc012 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc023 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc0123 i; rw [h] at hh; simp at hh
  · intro v
    apply hzero
    · intro i h; have hh := hc012 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc023 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc0123 i; rw [h] at hh; simp at hh
  · intro C u v hu hv huv hnon
    apply hzero
    · intro i h
      have hcl := window_clique (n := n) (i := i.val) (T := ({0,1,2} : Finset ℕ)) (by intro k hk; simp only [mem_insert, mem_singleton] at hk ⊢; tauto)
      rw [h] at hcl
      exact hnon (hcl u hu v hv huv)
    · intro i h
      have hcl := window_clique (n := n) (i := i.val) (T := ({0,2,3} : Finset ℕ)) (by intro k hk; simp only [mem_insert, mem_singleton] at hk ⊢; tauto)
      rw [h] at hcl
      exact hnon (hcl u hu v hv huv)
    · intro i h
      have hcl := window_clique (n := n) (i := i.val) (T := ({0,1,2,3} : Finset ℕ)) (subset_refl _)
      rw [h] at hcl
      exact hnon (hcl u hu v hv huv)

theorem setFunction_normalized (n : ℕ) : TranslationNormalized (setFunction n) :=
  ((cliqueSupported_iff (graph n) (coefficients n)).mp (coefficients_supported n)).1

theorem setFunction_graphical (n : ℕ) : Graphical (graph n) (setFunction n) :=
  ((cliqueSupported_iff (graph n) (coefficients n)).mp (coefficients_supported n)).2

theorem zeta_singleCoefficient {V : Type*} [Fintype V] [DecidableEq V] (C : Finset V) :
    zeta (Pi.single C 1) = setMonomial C := by
  classical
  funext S
  simp [zeta, setMonomial, Pi.single_apply, eq_comm]

/-- Exact correspondence with the paper's two triple sums minus the tetrahedron
sum, before changing the labels from `0,...,n-1` to `1,...,n`. -/
theorem setFunction_expansion (n : ℕ) :
    setFunction n =
      (∑ i : Fin (n-2), setMonomial (window n i.val {0,1,2})) +
      (∑ i : Fin (n-3), setMonomial (window n i.val {0,2,3})) -
      (∑ i : Fin (n-3), setMonomial (window n i.val {0,1,2,3})) := by
  change zetaLinear (coefficients n) = _
  rw [coefficients, map_sub, map_add, map_sum, map_sum, map_sum]
  simp only [show ∀ C : Finset (Fin n), zetaLinear (Pi.single C 1) = setMonomial C from
    fun C => zeta_singleCoefficient C]

end Path
end GraphicalZonotopes
