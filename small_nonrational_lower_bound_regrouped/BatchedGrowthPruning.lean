module
prelude
public import GrowthBitsets
public import GrowthRenaming

@[expose] public section

/-!
# Batched necessary exclusions

Bitsets summarize independently justified local exclusions. Their soundness is
proved for every target boundary. The cache laws are elementary relations to
literal ridge membership, pair compatibility, and cell kind; concrete cache
certificates must prove these laws before a search can use them.
-/

namespace Papers.RationalityTen.BatchedGrowthPruning

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open ConcreteGrowth GrowthBitsets

variable {n r : Nat}

structure Cache (ridgeList : Fin n → List (Fin r))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat) where
  candidates : Fin r → Nat
  incompatible : Fin n → Nat
  kinds : Nat → Nat
  keys : List Nat
  candidates_exact : ∀ q c, bitAt (candidates q) c.val = has (ridgeList c) q
  incompatible_sound : ∀ a c, bitAt (incompatible a) c.val = true → compatible a c = false
  kind_sound : ∀ k, k ∈ keys → ∀ c, bitAt (kinds k) c.val = true → kind c = k

structure ClosedWitness (n r : Nat) where
  ridge : Fin r
  first : Fin n
  second : Fin n

def closedWitnessCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (selected : Nat) (w : ClosedWitness n r) : Bool :=
  ((decide (w.first ≠ w.second) && bitAt selected w.first.val) &&
      bitAt selected w.second.val) &&
    (bitAt (cache.candidates w.ridge) w.first.val &&
      bitAt (cache.candidates w.ridge) w.second.val)

theorem closedWitnessCheck_sound {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (S : List (Fin n))
    (selected : Nat) (hselected : selected = ofList S) (w : ClosedWitness n r)
    (hcheck : closedWitnessCheck cache selected w = true) :
    w.first ≠ w.second ∧ w.first ∈ S ∧ w.second ∈ S ∧
      has (ridgeList w.first) w.ridge = true ∧ has (ridgeList w.second) w.ridge = true := by
  obtain ⟨hleft, hridges⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hhead, hsecond⟩ := Bool.and_eq_true_iff.mp hleft
  obtain ⟨hne, hfirst⟩ := Bool.and_eq_true_iff.mp hhead
  obtain ⟨hrfirst, hrsecond⟩ := Bool.and_eq_true_iff.mp hridges
  rw [hselected, bitAt_ofList] at hfirst hsecond
  rw [cache.candidates_exact] at hrfirst hrsecond
  exact ⟨of_decide_eq_true hne, hfirst, hsecond, hrfirst, hrsecond⟩

def quotaMask {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat) (S : List (Fin n)) : Nat :=
  unionValues (fun k => if quota k ≤ kindCount kind S k then cache.kinds k else 0) cache.keys

def blockedMask {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (S : List (Fin n)) (selected : Nat) (closed : List (ClosedWitness n r)) : Nat :=
  Nat.lor (Nat.lor (Nat.lor selected (unionValues cache.incompatible S))
    (quotaMask cache quota S)) (unionValues (fun w => cache.candidates w.ridge) closed)

theorem blockedMask_sound {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (S B : List (Fin n)) (selected : Nat) (closed : List (ClosedWitness n r))
    (hselected : selected = ofList S)
    (hclosed : closed.all (closedWitnessCheck cache selected) = true)
    (hB : Target (fun c => has (ridgeList c)) compatible kind quota B)
    (hsub : Included (family S) (family B)) (hnd : S.Nodup)
    (c : Fin n) (hcB : family B c = true) (hcS : has S c = false) :
    bitAt (blockedMask cache quota S selected closed) c.val = false := by
  have hsub' : S ⊆ B := by
    intro a ha
    exact (has_true B a).mp (hsub a ((has_true S a).mpr ha))
  have hcB' : c ∈ B := (has_true B c).mp hcB
  have hcS' : c ∉ S := by
    intro hc
    exact Bool.noConfusion (hcS.symm.trans ((has_true S c).mpr hc))
  have hselectedFalse : bitAt selected c.val = false := by
    rw [hselected, bitAt_ofList_eq_has]
    exact hcS
  have hbadFalse : bitAt (unionValues cache.incompatible S) c.val = false := by
    cases hbit : bitAt (unionValues cache.incompatible S) c.val with
    | false => rfl
    | true =>
      obtain ⟨a, ha, hbad⟩ := (bitAt_unionValues _ _ _).mp hbit
      have hne : a ≠ c := fun heq => hcS' (heq ▸ ha)
      have hgood := hB.pairwise a c (hsub' ha) hcB' hne
      exact False.elim (Bool.noConfusion ((cache.incompatible_sound a c hbad).symm.trans hgood))
  have hquotaFalse : bitAt (quotaMask cache quota S) c.val = false := by
    cases hbit : bitAt (quotaMask cache quota S) c.val with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hkindbit⟩ := (bitAt_unionValues _ _ _).mp hbit
      by_cases hexhausted : quota k ≤ kindCount kind S k
      · have hkc : kind c = k := cache.kind_sound k hk c (by simpa only [if_pos hexhausted] using hkindbit)
        have hlt := Nat.lt_of_lt_of_le (kindCount_lt kind S B c hnd hsub' hcB' hcS')
          (hB.budget (kind c))
        rw [hkc] at hlt
        exact False.elim (Nat.not_le_of_lt hlt hexhausted)
      · simp only [if_neg hexhausted, bitAt_zero] at hkindbit
        exact False.elim (Bool.noConfusion hkindbit)
  have hclosedFalse :
      bitAt (unionValues (fun w => cache.candidates w.ridge) closed) c.val = false := by
    cases hbit : bitAt (unionValues (fun w => cache.candidates w.ridge) closed) c.val with
    | false => rfl
    | true =>
      obtain ⟨w, hw, hcw⟩ := (bitAt_unionValues _ _ _).mp hbit
      have hvalid := closedWitnessCheck_sound cache S selected hselected w
        (List.all_eq_true.mp hclosed w hw)
      have haB := (has_true B w.first).mpr (hsub' hvalid.2.1)
      have hbB := (has_true B w.second).mpr (hsub' hvalid.2.2.1)
      rw [cache.candidates_exact] at hcw
      rcases hB.no_three w.ridge w.first w.second c
        ⟨haB, hvalid.2.2.2.1⟩ ⟨hbB, hvalid.2.2.2.2⟩ ⟨hcB, hcw⟩ with heq | heq | heq
      · exact False.elim (hvalid.1 heq)
      · exact False.elim (hcS' (heq ▸ hvalid.2.1))
      · exact False.elim (hcS' (heq ▸ hvalid.2.2.1))
  simp only [blockedMask, bitAt_or, hselectedFalse, hbadFalse, hquotaFalse, hclosedFalse]
  rfl

#print axioms blockedMask_sound

end Papers.RationalityTen.BatchedGrowthPruning
