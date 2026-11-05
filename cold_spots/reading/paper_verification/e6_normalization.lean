module

public import PaperVerification.E6Roots

@[expose] public section

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem triQ_integer_nonzero {m : EisInt} (hm : m≠0) : 1 ≤ triQ (eisEmbed m) := by
  let q : ℤ := m.1^2-m.1*m.2+m.2^2
  have hq : triQ (eisEmbed m)=(q:ℝ) := by dsimp [q,triQ,eisEmbed]; push_cast; ring
  have hp : 0 < triQ (eisEmbed m) := by
    apply lt_of_le_of_ne (triQ_nonneg _)
    intro hz
    have hl := triQ_lower (eisEmbed m)
    rw [← hz] at hl
    have h1 : (m.1:ℝ)=0 := by
      dsimp [eisEmbed] at hl
      nlinarith [sq_nonneg (m.1:ℝ),sq_nonneg (m.2:ℝ)]
    have h2 : (m.2:ℝ)=0 := by
      dsimp [eisEmbed] at hl
      nlinarith [sq_nonneg (m.1:ℝ),sq_nonneg (m.2:ℝ)]
    apply hm
    apply Prod.ext
    · exact_mod_cast h1
    · exact_mod_cast h2
  have hi : 0 < q := by rw [hq] at hp; exact_mod_cast hp
  have hi' : (1:ℤ) ≤ q := by omega
  rw [hq]
  exact_mod_cast hi'

theorem l6_minimal_squared_norm {z : TriTriple} (hz : z ∈ l6Set) (hne : z≠0) :
    1 ≤ triTripleSqDist z 0 := by
  obtain ⟨⟨r,m⟩,rfl⟩ := hz
  by_cases hr : r=0
  · subst r
    have hm : ∃ i, m i≠0 := by
      by_contra h
      push_neg at h
      apply hne
      funext i
      simp [l6Point,h i]
    obtain ⟨i,hi⟩ := hm
    have ht := triQ_integer_nonzero hi
    have hs : triQ (eisEmbed (m i)) ≤ ∑ j, triQ (eisEmbed (m j)) :=
      Finset.single_le_sum (fun j hj ↦ triQ_nonneg (eisEmbed (m j))) (Finset.mem_univ i)
    simpa [triTripleSqDist,l6Point] using ht.trans hs
  · have hb (i : Fin 3) : 1/3 ≤ triQ (l6Point (r,m) i) := by
      fin_cases r
      · exact (hr rfl).elim
      · have h := triangularDepth_le (-triC) (m i)
        rw [triangularDepth_even,triangularDepth_c] at h
        change 1/3 ≤ triQ (l6Point ((1 : ZMod 3),m) i)
        simp only [l6Point,zmodThree_val_one,Nat.cast_one,one_smul]
        simpa only [sub_neg_eq_add] using h
      · have he : eisEmbed (m i)+(2:ℝ)•triC=eisEmbed (m i+(1,-1))-triC := by
          rw [map_add]
          ext <;> dsimp [eisEmbed,triC] <;> ring
        have h := triangularDepth_le triC (m i+(1,-1))
        rw [triangularDepth_c] at h
        change 1/3 ≤ triQ (l6Point ((2 : ZMod 3),m) i)
        simp only [l6Point,zmodThree_val_two,Nat.cast_ofNat]
        rw [he]
        exact h
    have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) ↦ hb i)
    norm_num [triTripleSqDist] at hs ⊢
    exact hs

theorem e6PhysicalPoint_sqDist (z w : TriTriple) :
    sqDist (e6PhysicalPoint z) (e6PhysicalPoint w)=2*triTripleSqDist z w := by
  rw [e6PhysicalPoint,e6PhysicalPoint,sqDist_scaleVec,
    Real.sq_sqrt (by norm_num),triTripleFlatten_sqDist]

theorem e6PhysicalPoint_zero : e6PhysicalPoint 0=0 := by
  funext j
  refine Fin.addCases (m:=3) (n:=3) (fun i ↦ ?_) (fun i ↦ ?_) j <;>
    simp [e6PhysicalPoint,scaleVec,triTripleFlatten, -Fin.natAdd_eq_addNat]

/-- The lattice normalization in Theorem 1.1 has minimum squared norm exactly two. -/
theorem e6_minimal_squared_norm :
    (∀ x ∈ e6Set, x≠0 → 2 ≤ sqDist x 0) ∧
      e6SimpleRoot 1 ∈ e6Set ∧ sqDist (e6SimpleRoot 1) 0=2 := by
  constructor
  · rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩ hne
    have hzn : z≠0 := by intro h; subst z; exact hne e6PhysicalPoint_zero
    have h := l6_minimal_squared_norm hz hzn
    change 2 ≤ sqDist (e6PhysicalPoint z) 0
    rw [← e6PhysicalPoint_zero,e6PhysicalPoint_sqDist]
    linarith
  · constructor
    · apply (e6Set_simpleRoot_span _).mpr
      refine ⟨Pi.single 1 1,?_⟩
      simp [Pi.single_apply]
    · have h := e6SimpleRoot_gram 1 1
      simpa [sqDist,pow_two,e6Cartan] using h

end PaperVerification.ColdSpots
