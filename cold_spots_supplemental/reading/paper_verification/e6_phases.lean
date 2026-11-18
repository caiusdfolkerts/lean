module

public import PaperVerification.E6Coordinates
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triPhasePoint (r : ZMod 3) : TriPoint := (r.val : ℝ)•triC

lemma triPhase_difference_value (F : TriPoint → ℝ) (a b : ℝ)
    (h0 : F 0=a) (h1 : F triC=b) (hn1 : F (-triC)=b)
    (h2 : F ((2:ℝ)•triC)=b) (hn2 : F (-(2:ℝ)•triC)=b) (r s : ZMod 3) :
    F (triPhasePoint r-triPhasePoint s)=if r=s then a else b := by
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have hv0 : (0 : ZMod 3).val = 0 := by decide
  have hn2' : F (-((2 : ℝ) • triC)) = b := by simpa only [neg_smul] using hn2
  have hsub12 : triC - (2 : ℝ) • triC = -triC := by
    rw [two_smul]
    abel
  have hsub21 : (2 : ℝ) • triC - triC = triC := by
    rw [two_smul]
    abel
  rcases hcases r with rfl | rfl | rfl <;>
    rcases hcases s with rfl | rfl | rfl <;>
    norm_num [triPhasePoint, ← sub_smul, hv0, zmodThree_val_one,
      zmodThree_val_two, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
      h0, h1, hn1, h2, hn2, hn2', hsub12, hsub21]

theorem triangularGaussian_phases {α : ℝ} (hα : 0 < α) (r s : ZMod 3) :
    triangularGaussian α (triPhasePoint r-triPhasePoint s)=
      if r=s then triangularGaussian α 0 else triangularGaussian α triC := by
  apply triPhase_difference_value _ _ _ rfl rfl
  · exact triangularGaussian_even _ _
  · have h := triangularGaussian_two_c α 0
    simpa only [zero_add,zero_sub,triangularGaussian_even] using h
  · rw [neg_smul,triangularGaussian_even]
    have h := triangularGaussian_two_c α 0
    simpa only [zero_add,zero_sub,triangularGaussian_even] using h

theorem triangularDepth_phases (r s : ZMod 3) :
    triangularDepth (triPhasePoint r-triPhasePoint s)=if r=s then 0 else 1/3 := by
  apply triPhase_difference_value _ _ _ triangularDepth_zero triangularDepth_c
  · rw [triangularDepth_even,triangularDepth_c]
  · have he : (2:ℝ)•triC = -triC+eisEmbed (1,-1) := by
      ext <;> norm_num [triC,eisEmbed]
    rw [he,triangularDepth_periodic,triangularDepth_even,triangularDepth_c]
  · rw [neg_smul,triangularDepth_even]
    have he : (2:ℝ)•triC = -triC+eisEmbed (1,-1) := by
      ext <;> norm_num [triC,eisEmbed]
    rw [he,triangularDepth_periodic,triangularDepth_even,triangularDepth_c]

def E6PhaseConfiguration (z : TriTriple) (r : Fin 3 → ZMod 3) : Prop :=
  ∃ m : Fin 3 → EisInt, ∀ i, z i=eisEmbed (m i)+triPhasePoint (r i)

def E6BalancedPhases (z : TriTriple) : Prop :=
  ∃ r : Fin 3 → ZMod 3, Function.Bijective r ∧ E6PhaseConfiguration z r

theorem exists_E6PhaseConfiguration_iff (z : TriTriple) :
    (∃ r, E6PhaseConfiguration z r) ↔ ∀ i, TriPhase (z i) := by
  constructor
  · rintro ⟨r,m,hm⟩ i
    exact ⟨r i,m i,hm i⟩
  · intro h
    choose r m hm using h
    exact ⟨r,m,hm⟩

def e6GaussianProfile (a b : ℝ) (r : Fin 3 → ZMod 3) (s : ZMod 3) : ℝ :=
  ∏ i, if r i=s then a else b

def e6DepthProfile (r : Fin 3 → ZMod 3) (s : ZMod 3) : ℝ :=
  ∑ i, if r i=s then (0:ℝ) else 1/3

theorem l6Gaussian_of_phases {α : ℝ} (hα : 0 < α) {z : TriTriple} {r : Fin 3 → ZMod 3}
    (hr : E6PhaseConfiguration z r) :
    l6Gaussian α z=∑ s : ZMod 3, e6GaussianProfile
      (triangularGaussian α 0) (triangularGaussian α triC) r s := by
  obtain ⟨m,hm⟩ := hr
  rw [l6Gaussian_cosets hα]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.prod_congr rfl
  intro i hi
  rw [hm i,show eisEmbed (m i)+triPhasePoint (r i)-(s.val:ℝ)•triC =
    (triPhasePoint (r i)-triPhasePoint s)+eisEmbed (m i) by dsimp [triPhasePoint]; abel,
    triangularGaussian_periodic,triangularGaussian_phases hα]

theorem l6CosetDepth_of_phases {z : TriTriple} {r : Fin 3 → ZMod 3}
    (hr : E6PhaseConfiguration z r) (s : ZMod 3) :
    l6CosetDepth z s=e6DepthProfile r s := by
  obtain ⟨m,hm⟩ := hr
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm i,show eisEmbed (m i)+triPhasePoint (r i)-(s.val:ℝ)•triC =
    (triPhasePoint (r i)-triPhasePoint s)+eisEmbed (m i) by dsimp [triPhasePoint]; abel,
    triangularDepth_periodic,triangularDepth_phases]

lemma bijective_fin3_zmod3_iff (r : Fin 3 → ZMod 3) :
    Function.Bijective r ↔ r 0≠r 1 ∧ r 0≠r 2 ∧ r 1≠r 2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  simp only [Fintype.card_fin,ZMod.card,eq_self_iff_true,true_and,and_true]
  constructor
  · intro h
    exact ⟨fun he ↦ by have := h he; norm_num at this,
      fun he ↦ by have := h he; norm_num at this,
      fun he ↦ by have := h he; norm_num at this⟩
  · rintro ⟨h01,h02,h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

lemma e6GaussianProfile_eq_iff (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (r : Fin 3 → ZMod 3) :
    (e6GaussianProfile a b r 0=e6GaussianProfile a b r 1 ∧
      e6GaussianProfile a b r 1=e6GaussianProfile a b r 2) ↔ Function.Bijective r := by
  rw [bijective_fin3_zmod3_iff]
  have ha : 0 < a := hb.trans hab
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hgap : 0 < a*b*(a-b) := by positivity
  have hgap2 : 0 < (a-b)*(a^2+a*b+b^2) := by positivity
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have habne : a ≠ b := ne_of_gt hab
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  rcases hcases (r 0) with h0 | h0 | h0 <;>
    rcases hcases (r 1) with h1 | h1 | h1 <;>
    rcases hcases (r 2) with h2 | h2 | h2 <;>
    simp [e6GaussianProfile, Fin.prod_univ_three, h0, h1, h2,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
      ha0, hb0, habne, Ne.symm habne,
      mul_comm, mul_left_comm, mul_assoc] <;>
    first | (rintro ⟨he, hf⟩; nlinarith) | (intros; nlinarith)

lemma e6DepthProfile_eq_iff (r : Fin 3 → ZMod 3) :
    (e6DepthProfile r 0=2/3 ∧ e6DepthProfile r 1=2/3 ∧ e6DepthProfile r 2=2/3) ↔
      Function.Bijective r := by
  rw [bijective_fin3_zmod3_iff]
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  rcases hcases (r 0) with h0 | h0 | h0 <;>
    rcases hcases (r 1) with h1 | h1 | h1 <;>
    rcases hcases (r 2) with h2 | h2 | h2 <;>
    norm_num [e6DepthProfile, Fin.sum_univ_three, h0, h1, h2,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]

lemma e6GaussianProfile_bijective (a b : ℝ) {r : Fin 3 → ZMod 3}
    (hr : Function.Bijective r) (s : ZMod 3) : e6GaussianProfile a b r s=a*b^2 := by
  have h := (bijective_fin3_zmod3_iff r).mp hr
  have hcases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x=2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  rcases hcases (r 0) with h0 | h0 | h0 <;>
    rcases hcases (r 1) with h1 | h1 | h1 <;>
    rcases hcases (r 2) with h2 | h2 | h2 <;>
    rcases hcases s with rfl | rfl | rfl <;>
    simp_all [e6GaussianProfile, Fin.prod_univ_three, pow_two,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
      mul_comm, mul_left_comm, mul_assoc]

end PaperVerification.ColdSpots
