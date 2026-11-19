module

public import PaperVerification.E7TranslationClasses
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# The literal E₇* representatives in equation (26)

The arbitrary-real classification and the genuine translation quotient
are already proved. This module identifies those classes with the
displayed vectors x₀ and x₀+y_S, |S|=4. The actual E8 coordinate cosets
detect the only repetitions, and canonical subsets account for all 36 classes.
The completeness statement quantifies over the entire real hyperplane.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev E7FourSubset := {S : Finset (Fin 8) // S.card=4}
abbrev E7PaperIndex := Option E7FourSubset

def e7PaperAmbient : E7PaperIndex→Fin 8→ℝ
  | none => e8Axis
  | some S => e8Axis+(fun i=>if i∈S.val then 1/2 else 0)

def e7PaperDouble : E7PaperIndex→Fin 8→ℤ
  | none => fun i=>if i=0 then 2 else 0
  | some S => fun i=>(if i=0 then 2 else 0)+(if i∈S.val then 1 else 0)

def e7PaperHalfSum : E7PaperIndex→ℤ
  | none => 1
  | some _ => 3

def e7PaperCoordinates (p : E7PaperIndex) : Fin 8→ℤ :=
  e8IntCoordinates (e7PaperDouble p) (e7PaperHalfSum p)

def e7PaperBinary (p : E7PaperIndex) : BinaryWord8 :=
  fun i=>(e7PaperCoordinates p i : Binary)

def e7PaperPoint (p : E7PaperIndex) : zeroSumSpace := project8 (e7PaperAmbient p)

/-- This is the actual vector (1/2)1_S-(1/4)1 in the real hyperplane. -/
def e7PaperShift (S : E7FourSubset) : zeroSumSpace :=
  project8 (fun i=>if i∈S.val then 1/2 else 0)

theorem e7PaperShift_apply (S : E7FourSubset) (i : Fin 8) :
    e7PaperShift S i=(if i∈S.val then (1/2:ℝ) else 0)-1/4 := by
  have hs : (∑ j : Fin 8,if j∈S.val then (1/2:ℝ) else 0)=2 := by
    norm_num [S.property]
  simp only [e7PaperShift,project8_apply,hs]
  ring

@[simp] theorem e7PaperPoint_none : e7PaperPoint none=e7Witness := rfl

@[simp] theorem e7PaperPoint_some (S : E7FourSubset) :
    e7PaperPoint (some S)=e7Witness+e7PaperShift S :=
  project8_add _ _

theorem e7Witness_apply (i : Fin 8) :
    e7Witness i=(if i=0 then (1:ℝ) else 0)-1/8 := by
  simp only [e7Witness,project8_apply,e8Axis_sum,e8Axis,intVec]
  split_ifs <;> norm_num

theorem e7PaperDouble_sum (p : E7PaperIndex) :
    (∑ i,e7PaperDouble p i)=e7PaperHalfSum p+e7PaperHalfSum p := by
  cases p with
  | none => norm_num [e7PaperDouble,e7PaperHalfSum]
  | some S => simp [e7PaperDouble,e7PaperHalfSum,Finset.sum_add_distrib,S.property]

theorem e7PaperAmbient_double (p : E7PaperIndex) :
    (fun i=>2*e7PaperAmbient p i)=intVec (e7PaperDouble p) := by
  funext i
  cases p with
  | none => simp [e7PaperAmbient,e7PaperDouble,e8Axis,intVec]
  | some S =>
    by_cases h0 : i=0 <;> by_cases hS : i∈S.val <;>
      norm_num [e7PaperAmbient,e7PaperDouble,e8Axis,intVec,h0,hS] <;>
        split_ifs <;> norm_num

theorem e7PaperAmbient_halfRoot (p : E7PaperIndex) :
    e7PaperAmbient p=e8HalfRootSum (e7PaperCoordinates p) := by
  have hroot := e8RootSum_coordinates (intVec (e7PaperDouble p))
  rw [e8RootCoordinates_int _ _ (e7PaperDouble_sum p)] at hroot
  have hhalf := e8HalfRootSum_double (e7PaperCoordinates p)
  have hdouble := e7PaperAmbient_double p
  funext i
  have h1 := congrFun hroot i
  have h2 := congrFun hhalf i
  have h3 := congrFun hdouble i
  change e8RootSum (fun j=>(e7PaperCoordinates p j:ℝ)) i=
    intVec (e7PaperDouble p) i at h1
  change 2*e8HalfRootSum (e7PaperCoordinates p) i=
    e8RootSum (fun j=>(e7PaperCoordinates p j:ℝ)) i at h2
  linarith

/-- Every displayed binary vector already satisfies the canonical first-bit condition. -/
private theorem e7PaperBinary_zero (p : E7PaperIndex) : e7PaperBinary p 0 = 0 := by
  simp only [e7PaperBinary, e7PaperCoordinates, e8IntCoordinates,
    Matrix.cons_val_zero, Int.cast_mul, Int.cast_ofNat, binary_two_eq_zero, zero_mul]

private theorem e7PaperAmbient_sum (p : E7PaperIndex) :
    (∑ i, e7PaperAmbient p i) = (e7PaperHalfSum p : ℝ) := by
  cases p with
  | none => simpa only [e7PaperAmbient, e7PaperHalfSum, Int.cast_one] using e8Axis_sum
  | some S =>
    have hs : (∑ i : Fin 8, if i ∈ S.val then (1/2 : ℝ) else 0) = 2 := by
      norm_num [S.property]
    change (∑ i : Fin 8, (e8Axis i + (if i ∈ S.val then (1/2 : ℝ) else 0))) = 3
    rw [Finset.sum_add_distrib, e8Axis_sum, hs]
    norm_num

/-- This uses the independently established E8 geometry, before any paper-representative
coverage or projected deepness theorem. -/
private theorem e7PaperAmbient_deep (p : E7PaperIndex) :
    IsDeepHole (dPlusSet 8) (e7PaperAmbient p) := by
  cases p with
  | none => exact (isDeepHole_E8_iff _).mpr e8Axis_folded_hole
  | some S =>
    let z : Fin 8 → ℤ := fun i => if i = 0 then 1 else 0
    have hx (i : Fin 8) : e7PaperAmbient (some S) i =
        (z i : ℝ) + (if i ∈ S.val then 1/2 else 0) := by
      simp only [e7PaperAmbient, Pi.add_apply, e8Axis, intVec, z]
    have hr (i : Fin 8) : foldedRadius (e7PaperAmbient (some S)) i =
        if i ∈ S.val then 1/2 else 0 := by
      by_cases hi : i ∈ S.val
      · rw [if_pos hi]
        exact (foldedRadius_eq_half_iff _ i).mpr
          ⟨z i, by simpa only [if_pos hi] using hx i⟩
      · rw [if_neg hi]
        exact (foldedRadius_eq_zero_iff _ i).mpr
          ⟨z i, by simpa only [if_neg hi, add_zero] using hx i⟩
    apply (isDeepHole_E8_iff _).mpr
    refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
    · intro i
      by_cases hi : i ∈ S.val
      · right
        simpa only [if_pos hi] using hr i
      · left
        simpa only [if_neg hi] using hr i
    · simp only [hr]
      norm_num [S.property]

private def e7PaperClass (p : E7PaperIndex) : E7HoleIndex := by
  have hdeep := e7PaperAmbient_deep p
  rw [e7PaperAmbient_halfRoot] at hdeep
  have hbinary := e8_deep_halfRoot_binary hdeep
  have hsum := e7PaperAmbient_sum p
  rw [e7PaperAmbient_halfRoot, e8HalfRootSum_sum] at hsum
  have hint : e8HalfSumInt (e7PaperCoordinates p) = e7PaperHalfSum p := by
    exact_mod_cast hsum
  have hodd : Odd (e7PaperHalfSum p) := by
    cases p with
    | none =>
      change Odd (1 : ℤ)
      exact ⟨0, by norm_num⟩
    | some S =>
      change Odd (3 : ℤ)
      exact ⟨1, by norm_num⟩
  have hpolar : e8BinaryPolar (e7PaperBinary p) e8BinaryRoot = 1 := by
    change e8BinaryPolar (fun i => (e7PaperCoordinates p i : Binary)) e8BinaryRoot = 1
    rw [← e8HalfSumInt_cast, hint]
    exact ZMod.intCast_eq_one_iff_odd.mpr hodd
  exact ⟨⟨e7PaperBinary p, hbinary⟩, hpolar, e7PaperBinary_zero p⟩

/-- Exact identification of every displayed representative with a canonical binary class. -/
theorem e7PaperBinary_to_class : ∀ p : E7PaperIndex, ∃ c : E7HoleIndex,
    e7PaperBinary p=c.val.val ∨ e7PaperBinary p=c.val.val+e8BinaryRoot := by
  intro p
  exact ⟨e7PaperClass p, Or.inl rfl⟩

def E7PaperEquivalent : E7PaperIndex→E7PaperIndex→Prop
  | none,none => True
  | some S,some T => S.val=T.val ∨ S.val=T.valᶜ
  | _,_ => False

instance (p q : E7PaperIndex) : Decidable (E7PaperEquivalent p q) := by
  cases p <;> cases q <;> unfold E7PaperEquivalent <;> infer_instance

private def e7HalfIndicator (S : Finset (Fin 8)) : Fin 8 → ℝ :=
  fun i => if i ∈ S then 1/2 else 0

private def e7PaperSupport : E7PaperIndex → Finset (Fin 8)
  | none => ∅
  | some S => S.val

private theorem e7PaperSupport_even (p : E7PaperIndex) :
    Even (e7PaperSupport p).card := by
  cases p with
  | none => norm_num [e7PaperSupport]
  | some S => change Even S.val.card; rw [S.property]; decide

private theorem e7PaperAmbient_support (p : E7PaperIndex) :
    e7PaperAmbient p = e8Axis + e7HalfIndicator (e7PaperSupport p) := by
  cases p with
  | none =>
    funext i
    change e8Axis i = e8Axis i +
      (if i ∈ (∅ : Finset (Fin 8)) then (1/2 : ℝ) else 0)
    simp
  | some S => rfl

/-- The two actual E8 coordinate cosets detect equality or complementation of supports. -/
private theorem e7HalfIndicator_sub_mem (S T : Finset (Fin 8)) (hT : Even T.card) :
    e7HalfIndicator S - e7HalfIndicator T ∈ dPlusSet 8 ↔ S = T ∨ S = Tᶜ := by
  constructor
  · rintro ⟨z, hz, he | he⟩
    · left
      apply Finset.ext
      intro i
      constructor
      · intro hi
        by_contra hni
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_pos hi, if_neg hni,
          sub_zero, intVec] at h
        exact integer_ne_half_shift (z i) 0 (by simpa only [Int.cast_zero, zero_add] using h.symm)
      · intro hi
        by_contra hni
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_neg hni, if_pos hi,
          zero_sub, intVec] at h
        apply integer_ne_half_shift (z i) (-1)
        norm_num
        linarith
    · right
      apply Finset.ext
      intro i
      rw [Finset.mem_compl]
      constructor
      · intro hi hti
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_pos hi, if_pos hti, sub_self] at h
        exact integer_ne_half_shift 0 (z i) (by simpa only [Int.cast_zero] using h)
      · intro hti
        by_contra hi
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_neg hi, if_neg hti, sub_self] at h
        exact integer_ne_half_shift 0 (z i) (by simpa only [Int.cast_zero] using h)
  · rintro (rfl | rfl)
    · simpa only [sub_self] using zero_mem_dPlusSet 8
    · refine ⟨fun i => if i ∈ T then -1 else 0, ?_, Or.inr ?_⟩
      · have hs : (∑ i : Fin 8, if i ∈ T then (-1 : ℤ) else 0) = -(T.card : ℤ) := by
          simp
        rw [hs]
        rcases hT with ⟨k, hk⟩
        refine ⟨-(k : ℤ), ?_⟩
        rw [hk]
        push_cast
        ring
      · funext i
        by_cases hi : i ∈ T <;>
          norm_num [e7HalfIndicator, Finset.mem_compl, hi]

private theorem e7PaperSupport_relation (p q : E7PaperIndex) :
    (e7PaperSupport p = e7PaperSupport q ∨
      e7PaperSupport p = (e7PaperSupport q)ᶜ) ↔ E7PaperEquivalent p q := by
  cases p with
  | none =>
    cases q with
    | none => simp [e7PaperSupport, E7PaperEquivalent]
    | some T =>
      change ((∅ : Finset (Fin 8)) = T.val ∨ ∅ = T.valᶜ) ↔ False
      constructor
      · rintro (h | h) <;>
          have hc := congrArg Finset.card h <;>
          norm_num [Finset.card_compl, T.property] at hc
      · exact False.elim
  | some S =>
    cases q with
    | none =>
      change (S.val = ∅ ∨ S.val = (∅ : Finset (Fin 8))ᶜ) ↔ False
      constructor
      · rintro (h | h) <;>
          have hc := congrArg Finset.card h <;>
          norm_num [Finset.card_compl, S.property] at hc
      · exact False.elim
    | some T => rfl

private theorem e7PaperBinary_eq_iff (p q : E7PaperIndex) :
    e7PaperBinary p = e7PaperBinary q ↔
      e7PaperAmbient p - e7PaperAmbient q ∈ dPlusSet 8 := by
  unfold e7PaperBinary
  rw [e7PaperAmbient_halfRoot p, e7PaperAmbient_halfRoot q]
  exact (e8HalfRootSum_sub_mem_iff (e7PaperCoordinates p) (e7PaperCoordinates q)).symm

/-- The only repetitions among the 71 displayed vectors are the two
complementary representatives for each four-subset class. -/
theorem e7PaperBinary_equivalence : ∀ p q : E7PaperIndex,
    (e7PaperBinary p=e7PaperBinary q ∨
      e7PaperBinary p=e7PaperBinary q+e8BinaryRoot) ↔ E7PaperEquivalent p q := by
  intro p q
  have hn : e7PaperBinary p ≠ e7PaperBinary q + e8BinaryRoot := by
    intro h
    have hi := congrFun h 0
    simp only [Pi.add_apply, e7PaperBinary_zero, e8BinaryRoot_zero, zero_add] at hi
    exact zero_ne_one hi
  rw [or_iff_left hn, e7PaperBinary_eq_iff, e7PaperAmbient_support p,
    e7PaperAmbient_support q, add_sub_add_left_eq_sub,
    e7HalfIndicator_sub_mem _ _ (e7PaperSupport_even q), e7PaperSupport_relation]

private abbrev E7CanonicalPaperSubset :=
  {S : Finset (Fin 8) // S.card = 4 ∧ (0 : Fin 8) ∉ S}

private abbrev E7CanonicalPaperIndex := Option E7CanonicalPaperSubset

private def e7CanonicalForget : E7CanonicalPaperIndex → E7PaperIndex
  | none => none
  | some S => some ⟨S.val, S.property.1⟩

private def e7CanonicalClass (p : E7CanonicalPaperIndex) : E7HoleIndex :=
  e7PaperClass (e7CanonicalForget p)

private theorem card_e7CanonicalPaperIndex : Fintype.card E7CanonicalPaperIndex = 36 := by
  have hs : Fintype.card E7CanonicalPaperSubset =
      (((Finset.univ : Finset (Fin 8)).erase 0).powersetCard 4).card := by
    apply Fintype.card_of_subtype
    intro S
    rw [Finset.mem_powersetCard, Finset.subset_erase]
    simp only [Finset.subset_univ, true_and]
    exact and_comm
  rw [Fintype.card_option, hs, Finset.card_powersetCard]
  norm_num <;> decide

private theorem e7CanonicalClass_injective : Function.Injective e7CanonicalClass := by
  intro p q h
  have hb := congrArg (fun c : E7HoleIndex => c.val.val) h
  change e7PaperBinary (e7CanonicalForget p) = e7PaperBinary (e7CanonicalForget q) at hb
  have he := (e7PaperBinary_equivalence _ _).mp (Or.inl hb)
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some T => exact False.elim he
  | some S =>
    cases q with
    | none => exact False.elim he
    | some T =>
      change S.val = T.val ∨ S.val = T.valᶜ at he
      rcases he with he | he
      · exact congrArg some (Subtype.ext he)
      · have h0 : (0 : Fin 8) ∈ S.val := by
          rw [he]
          exact Finset.mem_compl.mpr T.property.2
        exact (S.property.2 h0).elim

/-- Canonical four-subsets avoiding zero supply 35 classes, with the first representative
supplying the remaining class. The target cardinal was proved independently from E8. -/
theorem e7_class_to_paperBinary : ∀ c : E7HoleIndex, ∃ p : E7PaperIndex,
    c.val.val=e7PaperBinary p ∨ c.val.val=e7PaperBinary p+e8BinaryRoot := by
  have hbij : Function.Bijective e7CanonicalClass :=
    (Fintype.bijective_iff_injective_and_card e7CanonicalClass).mpr
      ⟨e7CanonicalClass_injective, by rw [card_e7CanonicalPaperIndex, card_e7HoleIndex]⟩
  intro c
  obtain ⟨p, hp⟩ := hbij.2 c
  refine ⟨e7CanonicalForget p, Or.inl ?_⟩
  have hv := congrArg (fun d : E7HoleIndex => d.val.val) hp
  change e7PaperBinary (e7CanonicalForget p) = c.val.val at hv
  exact hv.symm

theorem e7PaperPoint_difference_iff (p q : E7PaperIndex) :
    e7PaperPoint p-e7PaperPoint q∈e7ProjectedSet ↔ E7PaperEquivalent p q := by
  unfold e7PaperPoint
  rw [e7PaperAmbient_halfRoot,e7PaperAmbient_halfRoot,
    e7Projected_halfRoot_difference_iff]
  exact e7PaperBinary_equivalence p q

theorem e7PaperPoint_deep (p : E7PaperIndex) : IsE7DeepHole (e7PaperPoint p) := by
  obtain ⟨c,hc⟩ := e7PaperBinary_to_class p
  have hmem : e7PaperPoint p-e7ClassPoint c∈e7ProjectedSet := by
    unfold e7PaperPoint e7ClassPoint e8ClassPoint
    rw [e7PaperAmbient_halfRoot,e7Projected_halfRoot_difference_iff]
    change e7PaperBinary p = (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) ∨
      e7PaperBinary p = (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) + e8BinaryRoot
    simpa only [binary_val_cast] using hc
  have h := (isE7DeepHole_add_iff hmem (e7ClassPoint c)).mpr (e7ClassPoint_deep c)
  have he : e7ClassPoint c+(e7PaperPoint p-e7ClassPoint c)=e7PaperPoint p := by abel
  rwa [he] at h

/-- Equation (26), with full quantification over the actual real
hyperplane and membership in the actual E₇* lattice. -/
theorem isE7DeepHole_iff_paper (x : zeroSumSpace) :
    IsE7DeepHole x ↔ ∃ p : E7PaperIndex,x-e7PaperPoint p∈e7ProjectedSet := by
  constructor
  · intro hx
    obtain ⟨c,hc⟩ := e7DeepHole_coset_coverage hx
    obtain ⟨p,hp⟩ := e7_class_to_paperBinary c
    refine ⟨p,?_⟩
    have hcp : e7ClassPoint c-e7PaperPoint p∈e7ProjectedSet := by
      unfold e7PaperPoint e7ClassPoint e8ClassPoint
      rw [e7PaperAmbient_halfRoot,e7Projected_halfRoot_difference_iff]
      change (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) = e7PaperBinary p ∨
        (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) = e7PaperBinary p + e8BinaryRoot
      simpa only [binary_val_cast] using hp
    rw [← e7ProjectedAddSubgroup_coe] at hc hcp ⊢
    have he : x - e7PaperPoint p =
        (x - e7ClassPoint c) + (e7ClassPoint c - e7PaperPoint p) := by abel
    rw [he]
    exact e7ProjectedAddSubgroup.add_mem hc hcp
  · rintro ⟨p,hp⟩
    have h := (isE7DeepHole_add_iff hp (e7PaperPoint p)).mpr (e7PaperPoint_deep p)
    have he : e7PaperPoint p+(x-e7PaperPoint p)=x := by abel
    rwa [he] at h

theorem e7_paper_first_distinct (S : E7FourSubset) :
    e7PaperShift S∉e7ProjectedSet := by
  have h := (e7PaperPoint_difference_iff (some S) none).not.mpr (by simp [E7PaperEquivalent])
  simpa only [e7PaperPoint_some,e7PaperPoint_none,add_sub_cancel_left] using h

theorem e7_paper_subsets_same_class_iff (S T : E7FourSubset) :
    e7PaperShift S-e7PaperShift T∈e7ProjectedSet ↔ S.val=T.val ∨ S.val=T.valᶜ := by
  have h := e7PaperPoint_difference_iff (some S) (some T)
  simpa only [e7PaperPoint_some,add_sub_add_left_eq_sub,E7PaperEquivalent] using h

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.isE7DeepHole_iff_paper
#print axioms PaperVerification.ColdSpots.e7_paper_subsets_same_class_iff
