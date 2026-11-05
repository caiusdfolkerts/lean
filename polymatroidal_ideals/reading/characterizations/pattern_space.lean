import Characterizations.FiniteCover

/-! # The finite space of all required degree-sensitive patterns -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev DegreePattern (V : Type*) [Fintype V] [DecidableEq V] (s : ℕ) :=
  Σ T : {T : Finset V // T.card = s+3}, PointedTriple T.val

def RealizesPattern {s : ℕ} (o : VariableOrder V) (P : DegreePattern V s) : Prop :=
  CoversPoint (restrictedOrder o (Function.Embedding.subtype (· ∈ P.1.val))) P.2

theorem card_degreePattern (s : ℕ) : Nat.card (DegreePattern V s) =
    (Fintype.card V).choose (s+3) * ((s+3)*(s+2).choose 2) := by
  change Nat.card (Σ T : {T : Finset V // T.card = s+3}, PointedTriple T.val) = _
  rw [Nat.card_sigma]
  have hP (T : {T : Finset V // T.card = s+3}) :
      Nat.card (PointedTriple T.val) = (s+3)*(s+2).choose 2 := by
    rw [Nat.card_eq_fintype_card,card_pointedTriple,Fintype.card_coe,T.property]
    simp
  simp_rw [hP]
  simp [Fintype.card_finset_len]

theorem pointedTriple_count_formula (n : ℕ) (hn : 1 ≤ n) :
    n*(n-1).choose 2 = 3*n.choose 3 := by
  have hh := Nat.add_one_mul_choose_eq (n-1) 2
  have he : n-1+1 = n := by omega
  simpa [he,mul_comm] using hh

theorem card_degreePattern_paper (s : ℕ) (hn : 1 ≤ Fintype.card V) :
    Nat.card (DegreePattern V s) =
      Fintype.card V * (Fintype.card V-1).choose 2 * (Fintype.card V-3).choose s := by
  have hsmall : (s+3)*(s+2).choose 2 = 3*(s+3).choose 3 := by
    simpa using pointedTriple_count_formula (s+3) (by omega)
  rw [card_degreePattern,hsmall,pointedTriple_count_formula (Fintype.card V) hn]
  have hh := Nat.choose_mul (n := Fintype.card V) (k := s+3) (s := 3) (by omega)
  have he : s+3-3 = s := by omega
  rw [he] at hh
  nlinarith

theorem degreePattern_nonempty (s : ℕ) (hs : s+3 ≤ Fintype.card V) :
    Nonempty (DegreePattern V s) := by
  obtain ⟨T,hTsub,hTc⟩ := exists_subset_card_eq (show s+3 ≤ (univ : Finset V).card by simpa using hs)
  have hcard : 3 ≤ Fintype.card T := by rw [Fintype.card_coe,hTc]; omega
  obtain ⟨i,q,j,hiq,hij,hqj⟩ := exists_three_distinct hcard
  exact ⟨⟨⟨T,hTc⟩,⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩⟩⟩

theorem realizesPattern_probability {s : ℕ} (P : DegreePattern V s) :
    finiteFraction (fun o : VariableOrder V => RealizesPattern o P) =
      1 / ((s+3)*(s+2).choose 2 : ℕ) := by
  change finiteFraction (fun o : VariableOrder V => CoversPoint
    (restrictedOrder o (Function.Embedding.subtype (· ∈ P.1.val))) P.2) = _
  have hh := restricted_point_probability P.1.val (by rw [P.1.property]; omega) P.2
  simpa only [P.1.property,show s+3-1=s+2 by omega] using hh

theorem coversPatterns_iff_degreePattern {s : ℕ} (F : Set (VariableOrder V)) :
    CoversPatterns s F ↔ ∀ P : DegreePattern V s, ∃ o ∈ F,RealizesPattern o P := by
  constructor
  · intro hF P
    obtain ⟨i,q,hiq,hA⟩ := card_eq_two.mp P.2.2.property.2
    let j := P.2.1
    have hij : i ≠ j := (mem_erase.mp (P.2.2.property.1 (by simp [hA]))).1
    have hqj : q ≠ j := (mem_erase.mp (P.2.2.property.1 (by simp [hA]))).1
    have hiq' : i.val ≠ q.val := fun he => hiq (Subtype.ext he)
    have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hqj' : q.val ≠ j.val := fun he => hqj (Subtype.ext he)
    let C := P.1.val \ {i.val,q.val,j.val}
    have hCcap : C ⊆ tripleCap i.val q.val j.val := by
      intro x hx
      have hh := (mem_sdiff.mp hx).2
      simpa [tripleCap] using hh
    have hCcard : C.card = s := by
      have hsubset : ({i.val,q.val,j.val} : Finset V) ⊆ P.1.val := by
        simp [insert_subset_iff,i.property,q.property,j.property]
      dsimp only [C]
      rw [card_sdiff_of_subset hsubset,P.1.property]
      simp [hiq',hij',hqj']
    obtain ⟨o,ho,hp⟩ := hF i.val q.val j.val hiq' hij' hqj' C hCcap hCcard
    refine ⟨o,ho,i,q,hiq,hA,?_⟩
    exact (restricted_finalTriple_iff P.1.val o i q j).mpr hp
  · intro hF i q j hiq hij hqj C hC hCc
    let T := patternActive C i q j
    have hTc : T.card = s+3 := by rw [patternActive_card hiq hij hqj hC,hCc]
    let I : T := ⟨i,by simp [T,patternActive]⟩
    let Q : T := ⟨q,by simp [T,patternActive]⟩
    let J : T := ⟨j,by simp [T,patternActive]⟩
    have hIQ : I ≠ Q := fun he => hiq (congrArg Subtype.val he)
    have hIJ : I ≠ J := fun he => hij (congrArg Subtype.val he)
    have hQJ : Q ≠ J := fun he => hqj (congrArg Subtype.val he)
    let P : DegreePattern V s := ⟨⟨T,hTc⟩,⟨J,⟨{I,Q},
      by simp [insert_subset_iff,hIJ,hQJ],by simp [hIQ]⟩⟩⟩
    obtain ⟨o,ho,hp⟩ := hF P
    have hf : FinalTriple (restrictedOrder o (Function.Embedding.subtype (· ∈ T))) I Q J :=
      (coversPoint_pair_iff hIQ hIJ hQJ).mp hp
    have hpat := (restricted_finalTriple_iff T o I Q J).mp hf
    have hTC : T \ {i,q,j} = C := by
      ext x
      have hiC : i ∉ C := fun h => by simpa using hC h
      have hqC : q ∉ C := fun h => by simpa using hC h
      have hjC : j ∉ C := fun h => by simpa using hC h
      by_cases hxi : x = i <;> by_cases hxq : x = q <;> by_cases hxj : x = j <;>
        simp [T,patternActive,hxi,hxq,hxj,hiC,hqC,hjC]
    exact ⟨o,ho,by simpa only [I,Q,J,hTC] using hpat⟩

end Characterizations
