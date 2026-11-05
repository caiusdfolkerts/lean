module

public import Papers.GraphicalZonotopes.BookUpperBlocks
public import Papers.GraphicalZonotopes.AnchorBlockCounts

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

theorem cliqueCapacity_int_formula (s : ℕ) :
    (cliqueCapacity s : ℤ)=(s.choose 2 : ℤ)*(2 : ℤ)^(s-2)-(2 : ℤ)^s+(s : ℤ)+2 := by
  let S := (univ : Finset (Fin s))
  have hsum := blockDimensionSum_add_cliques S
  rw [sum_powerset_choose_two] at hsum
  have hcount := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => 2≤C.card)
  rw [small_subsets_card,card_powerset] at hcount
  change (nontrivialSubsets S).card+(S.card+1)=2^S.card at hcount
  have hcap := cliqueCapacity_eq_dimension_sum S
  have hScard : S.card=s := by simp [S]
  rw [hScard] at hsum hcount hcap
  have hsum' : (blockDimensionSum S : ℤ)+((nontrivialSubsets S).card : ℤ)=
      (s.choose 2 : ℤ)*(2 : ℤ)^(s-2) := by exact_mod_cast hsum
  have hcount' : ((nontrivialSubsets S).card : ℤ)+(s : ℤ)+1=(2 : ℤ)^s := by exact_mod_cast hcount
  have hcap' : (cliqueCapacity s : ℤ)=(blockDimensionSum S : ℤ)+1 := by exact_mod_cast hcap
  linarith

theorem cliqueCapacity_pred_le {s : ℕ} (hs : 1≤s) :
    cliqueCapacity (s-1)≤cliqueCapacity s := by
  let S := (univ : Finset (Fin s))
  let a : Fin s := ⟨0,by omega⟩
  have ha : a∈S := mem_univ _
  have h := blockDimensionSum_erase_add_anchor S a ha
  have hcap := cliqueCapacity_eq_dimension_sum S
  have hprev := cliqueCapacity_eq_dimension_sum (S.erase a)
  rw [card_erase_of_mem ha] at hprev
  have hScard : S.card=s := by simp [S]
  rw [hScard] at hcap hprev
  omega

theorem two_mul_le_choose_two {n : ℕ} (hn : 5≤n) : 2*n≤n.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  calc
    (2*n)*2=n*4 := by ring
    _ ≤ n*(n-1) := Nat.mul_le_mul_left n (by omega)

private theorem pow_pred_four {s : ℕ} (hs : 3≤s) :
    (2 : ℤ)^(s-1)=4*(2 : ℤ)^(s-3) := by
  have he : s-1=(s-3)+2 := by omega
  calc
    (2 : ℤ)^(s-1)=(2 : ℤ)^((s-3)+2) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_add]; norm_num; ring

private theorem pow_pred_two {s : ℕ} (hs : 3≤s) :
    (2 : ℤ)^(s-2)=2*(2 : ℤ)^(s-3) := by
  have he : s-2=(s-3)+1 := by omega
  calc
    (2 : ℤ)^(s-2)=(2 : ℤ)^((s-3)+1) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_succ]; ring

private theorem pow_eight {s : ℕ} (hs : 3≤s) :
    (2 : ℤ)^s=8*(2 : ℤ)^(s-3) := by
  have he : s=(s-3)+3 := by omega
  calc
    (2 : ℤ)^s=(2 : ℤ)^((s-3)+3) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_add]; norm_num; ring

theorem threshold_start_le_previous_capacity {s : ℕ} (hs : 6≤s) :
    2^(s-1)-s+1≤cliqueCapacity (s-1) := by
  have hpowge : s≤2^(s-1) := by
    have h := Nat.lt_two_pow_self (n := s-1)
    omega
  have hcast : ((2^(s-1)-s+1 : ℕ) : ℤ)=(2 : ℤ)^(s-1)-(s : ℤ)+1 := by
    rw [Nat.cast_add,Nat.cast_sub hpowge,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hchoose : (8 : ℤ)≤((s-1).choose 2 : ℤ) := by
    have h := two_mul_le_choose_two (show 5≤s-1 by omega)
    have h' : (8 : ℕ)≤(s-1).choose 2 := by omega
    exact_mod_cast h'
  have hnonneg : 0≤(((s-1).choose 2 : ℤ)-8)*(2 : ℤ)^(s-3) :=
    mul_nonneg (by omega) (by positivity)
  have hformula := cliqueCapacity_int_formula (s-1)
  have hexp : s-1-2=s-3 := by omega
  rw [hexp,pow_pred_four (by omega),Nat.cast_sub (show 1≤s by omega),Nat.cast_one] at hformula
  have hbound : ((2^(s-1)-s+1 : ℕ) : ℤ)≤(cliqueCapacity (s-1) : ℤ) := by
    rw [hcast,pow_pred_four (by omega)]
    nlinarith
  exact_mod_cast hbound

theorem bookUpperIntervalStart_int_formula {s : ℕ} (hs : 5≤s) :
    (bookUpperIntervalStart s : ℤ)=((s : ℤ)-2)*(2 : ℤ)^(s-1)+2*(s : ℤ)-2-(s.choose 2 : ℤ) := by
  have h := BookBlock_lower_sum (show 2≤s by omega)
  have h2 : 2≤(s-2)*2^(s-1)+2*s := by omega
  have hc : s.choose 2≤(s-2)*2^(s-1)+2*s-2 := by omega
  unfold bookUpperIntervalStart
  rw [Nat.cast_sub hc,Nat.cast_sub h2,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,
    Nat.cast_sub (show 2≤s by omega),Nat.cast_pow]
  norm_num

theorem upper_start_le_threshold_end {s : ℕ} (hs : 6≤s) :
    bookUpperIntervalStart s≤cliqueCapacity s-cliqueCapacity (s-1)+1 := by
  have hmono := cliqueCapacity_pred_le (show 1≤s by omega)
  have hchoose : (s.choose 2 : ℤ)=((s-1).choose 2 : ℤ)+(s : ℤ)-1 := by
    have h := Nat.choose_succ_succ (s-1) 1
    change (s-1+1).choose 2=(s-1).choose 1+(s-1).choose 2 at h
    have he : s-1+1=s := by omega
    have hc : s.choose 2=(s-1)+(s-1).choose 2 := by
      simpa only [he,Nat.choose_one_right] using h
    rw [hc,Nat.cast_add,Nat.cast_sub (show 1≤s by omega),Nat.cast_one]
    ring
  have hcpNat := two_mul_le_choose_two (show 5≤s-1 by omega)
  have hcsNat := two_mul_le_choose_two (show 5≤s by omega)
  have hcp : 2*((s : ℤ)-1)≤((s-1).choose 2 : ℤ) := by
    have h' : ((2*(s-1) : ℕ) : ℤ)≤((s-1).choose 2 : ℤ) := by exact_mod_cast hcpNat
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (show 1≤s by omega),Nat.cast_one] using h'
  have hcs : 2*(s : ℤ)≤(s.choose 2 : ℤ) := by exact_mod_cast hcsNat
  have hp : 0≤(((s-1).choose 2 : ℤ)-2*(s : ℤ)+2)*(2 : ℤ)^(s-3) :=
    mul_nonneg (by omega) (by positivity)
  have hgap : ((cliqueCapacity s-cliqueCapacity (s-1)+1 : ℕ) : ℤ)-
      (bookUpperIntervalStart s : ℤ)=
      (((s-1).choose 2 : ℤ)-2*(s : ℤ)+2)*(2 : ℤ)^(s-3)+
        (s.choose 2 : ℤ)-2*(s : ℤ)+4 := by
    rw [Nat.cast_add,Nat.cast_sub hmono,Nat.cast_one,
      bookUpperIntervalStart_int_formula (by omega),cliqueCapacity_int_formula,
      cliqueCapacity_int_formula]
    have hexp : s-1-2=s-3 := by omega
    rw [hexp,pow_pred_two (s:=s) (by omega),pow_eight (s:=s) (by omega),pow_pred_four (s:=s) (by omega),
      Nat.cast_sub (show 1≤s by omega),Nat.cast_one,hchoose]
    ring
  have hbound : (bookUpperIntervalStart s : ℤ)≤
      ((cliqueCapacity s-cliqueCapacity (s-1)+1 : ℕ) : ℤ) := by linarith
  exact_mod_cast hbound

end BooleanModule
end GraphicalZonotopes
