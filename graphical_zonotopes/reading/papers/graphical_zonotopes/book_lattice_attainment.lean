module

public import Papers.GraphicalZonotopes.BookEmbeddings
public import Papers.GraphicalZonotopes.BookIntervalArithmetic
public import Papers.GraphicalZonotopes.TwoAnchorBookCircuits
public import Papers.GraphicalZonotopes.ThresholdBookCircuits
public import Papers.GraphicalZonotopes.SmallCountPrincipal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
open BooleanModule

private theorem book_lattice_of_full_complement {s k M : ℕ}
    (h : ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(M : ℝ) • graphicalZonotope (cliqueBook s k)) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) M := by
  obtain ⟨f,hn,hi,he,hG,hd,hm,hl,R,hR,hRn,hQR⟩ := h
  apply LatticeExtremeAt.of_lattice_complement hn hi he hG _ hR hRn hQR
  simpa only [FullDimension,Fintype.card_sum,Fintype.card_fin] using hd

theorem book_lattice_small {s k : ℕ} (hs : 2≤s) (hk : 1≤k) (hcap : k≤s.choose 2) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) := by
  have h := book_lattice_of_full_complement (small_count_lattice_books s k hs hk hcap)
  apply h.mono_dilation
  simpa only [one_mul] using Nat.mul_le_mul_right k (show 1≤s-1 by omega)

theorem book_lattice_threshold {s k : ℕ} (hs : 3≤s)
    (hklo : 2^(s-1)-s+1≤k) (hkhi : k≤cliqueCapacity s-cliqueCapacity (s-1)+1) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) := by
  have h := book_lattice_of_full_complement (threshold_book_interval hs hklo hkhi)
  apply h.mono_dilation
  simpa only [one_mul] using Nat.mul_le_mul_right k (show 1≤s-1 by omega)

theorem book_lattice_upper {s k : ℕ} (hs : 5≤s)
    (hklo : bookUpperIntervalStart s≤k) (hkhi : k≤cliqueCapacity s) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) :=
  book_lattice_of_full_complement (book_upper_interval hs hklo hkhi)

theorem book_lattice_four_bridge {k : ℕ} (hklo : 12≤k) (hkhi : k≤14) :
    LatticeExtremeAt (cliqueBook 4 k) (4+k-1) ((4-1)*k) := by
  have h := book_lattice_of_full_complement (two_threshold_four_bridge hklo hkhi)
  exact h.mono_dilation (Nat.mul_le_mul_right k (by decide : 2≤4-1))

theorem book_lattice_five_bridge {k : ℕ} (hklo : 39≤k) (hkhi : k≤53) :
    LatticeExtremeAt (cliqueBook 5 k) (5+k-1) ((5-1)*k) := by
  have h := book_lattice_of_full_complement (two_threshold_five_bridge hklo hkhi)
  exact h.mono_dilation (Nat.mul_le_mul_right k (by decide : 2≤5-1))

/-- Full dimensional integral attainment for every book below its exact
capacity. The induction uses actual graph embeddings and the proved overlap
inequalities, including the four- and five-hub bridges. -/
theorem book_lattice_full (s : ℕ) : ∀ k : ℕ,2≤s → 1≤k → k≤cliqueCapacity s →
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro k hs hk hcap
    by_cases hsmall : k≤s.choose 2
    · exact book_lattice_small hs hk hsmall
    have hs4 : 4≤s := by
      by_contra hn
      have hcases : s=2 ∨ s=3 := by omega
      rcases hcases with rfl | rfl <;> norm_num [cliqueCapacity,Nat.choose] at hcap hsmall <;> omega
    by_cases hsEq4 : s=4
    · subst s
      have hcap' : k≤14 := by simpa [cliqueCapacity,Nat.choose] using hcap
      by_cases h12 : k≤12
      · apply book_lattice_threshold (by decide)
        · norm_num [Nat.choose] at hsmall
          norm_num
          omega
        · norm_num [cliqueCapacity,Nat.choose]
          exact h12
      · exact book_lattice_four_bridge (by omega) hcap'
    by_cases hsEq5 : s=5
    · subst s
      have hcap' : k≤55 := by simpa [cliqueCapacity,Nat.choose] using hcap
      have hk11 : 11≤k := by norm_num [Nat.choose] at hsmall; omega
      by_cases hkEq11 : k=11
      · subst k
        have hprev := ih 4 (by decide) 12 (by decide) (by decide)
          (by norm_num [cliqueCapacity,Nat.choose])
        have hp := book_lattice_promote hprev
        exact hp.mono_dilation (by decide)
      by_cases h42 : k≤42
      · apply book_lattice_threshold (by decide)
        · norm_num
          omega
        · norm_num [cliqueCapacity,Nat.choose]
          exact h42
      by_cases h53 : k≤53
      · exact book_lattice_five_bridge (by omega) h53
      · apply book_lattice_upper (by decide)
        · norm_num [bookUpperIntervalStart,Nat.choose]
          omega
        · exact hcap
    have hs6 : 6≤s := by omega
    by_cases hprev : k+1≤cliqueCapacity (s-1)
    · have hp := ih (s-1) (by omega) (k+1) (by omega) (by omega) hprev
      have hpromote := book_lattice_promote hp
      have he : s-1+1=s := by omega
      rw [he] at hpromote
      apply hpromote.mono_dilation
      have hchoose := two_mul_le_choose_two (show 5≤s by omega)
      have hkbig : s-2≤k := by omega
      have he' : s-1-1=s-2 := by omega
      have he'' : s-1=(s-2)+1 := by omega
      rw [he',he'']
      nlinarith
    · have hkstart : 2^(s-1)-s+1≤k :=
        (threshold_start_le_previous_capacity hs6).trans (by omega)
      by_cases hthreshold : k≤cliqueCapacity s-cliqueCapacity (s-1)+1
      · exact book_lattice_threshold (by omega) hkstart hthreshold
      · exact book_lattice_upper (by omega)
          ((upper_start_le_threshold_end hs6).trans (by omega)) hcap

/-- Exact lattice attainment of the dimension formula for all branch counts,
including counts above capacity. The extra vertices are genuine unused
coordinates, introduced by an injective extension of the actual set function. -/
theorem book_lattice_attainment (s k : ℕ) (hs : 2≤s) (hk : 1≤k) :
    LatticeExtremeAt (cliqueBook s k)
      (min (s+k-1) (s+cliqueCapacity s-1)) ((s-1)*min k (cliqueCapacity s)) := by
  have hcapPos : 1≤cliqueCapacity s := by unfold cliqueCapacity; omega
  let m := min k (cliqueCapacity s)
  have hm : 1≤m := le_min hk hcapPos
  have h := book_lattice_full s m hs hm (min_le_right _ _)
  have he := book_lattice_add_outer (min_le_left k (cliqueCapacity s)) h
  have hd : s+m-1=min (s+k-1) (s+cliqueCapacity s-1) := by
    dsimp only [m]
    by_cases hkc : k≤cliqueCapacity s
    · rw [min_eq_left hkc,min_eq_left (by omega)]
    · rw [min_eq_right (by omega),min_eq_right (by omega)]
  rw [hd] at he
  exact he

end GraphicalZonotopes
