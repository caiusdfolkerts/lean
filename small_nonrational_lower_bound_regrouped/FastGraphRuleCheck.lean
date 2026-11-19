module
prelude
public import GraphGrowthRuleSoundness

@[expose] public section

/-!
# Short certificates for capacity bounds

A capacity calculation never needs to count beyond the remaining quota.
Whenever the available cells are fewer, a short covering list certifies the
upper bound by one mask inclusion.  Otherwise the quota itself is sufficient.
The resulting checker implies the previously proved rule checker.
-/

namespace Papers.RationalityTen.FastGraphRuleCheck

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthBitsets
open GraphGrowthConstraints FiniteMaskSets

variable {n r e v k : Nat}

abbrev Bounds (n : Nat) := List (Option (List (Fin n)))

theorem card_le_length_of_cover (mask : Nat) (xs : List (Fin n))
    (h : Nat.land mask (PrimitiveBitsetGrowth.mask xs) = mask) :
    card n mask ≤ xs.length := by
  apply List.Nodup.length_le_of_subset (elements_nodup n mask)
  intro c hc
  have hh := congrArg (fun bits => bits.testBit c.val) h
  have hm := (mem_elements c).mp hc
  have hx : (ofList xs).testBit c.val = true := by
    simpa only [PrimitiveBitsetGrowth.mask_eq, testBit_land, hm,
      Bool.true_and] using hh
  exact (bitAt_ofList xs c).mp ((bitAt_eq_testBit _ _).trans hx)

def boundCheck (mask : Nat) : Option (List (Fin n)) → Bool
  | none => true
  | some xs => decide (Nat.land mask (PrimitiveBitsetGrowth.mask xs) = mask)

def boundValue (remaining : Nat) : Option (List (Fin n)) → Nat
  | none => remaining
  | some xs => min remaining xs.length

theorem boundCheck_sound (mask remaining : Nat) (b : Option (List (Fin n)))
    (h : boundCheck mask b = true) :
    min remaining (card n mask) ≤ boundValue remaining b := by
  cases b with
  | none => simp only [boundValue]; omega
  | some xs =>
    have hc := card_le_length_of_cover mask xs (of_decide_eq_true h)
    simp only [boundValue]
    omega

private theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ a ∈ xs, f a ≤ g a) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self))
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

def vertexBoundCheck (D : Problem n r e v k) (available : Nat)
    (a : Fin v) (bounds : Bounds n) : Bool :=
  (List.finRange k).all fun j =>
    boundCheck
      (Nat.land available (Nat.land (D.cache.kinds j.val) (D.vertexRows a)))
      (bounds.getD j.val none)

def vertexBound (D : Problem n r e v k) (S : List (Fin n))
    (bounds : Bounds n) (a : Fin v) : Nat :=
  vertexCount D S a + ((List.finRange k).map fun j =>
    boundValue (D.quota j.val - kindCount D.kind S j.val)
      (bounds.getD j.val none)).sum

theorem vertexBoundCheck_sound (D : Problem n r e v k) (S : List (Fin n))
    (available : Nat) (bounds : Bounds n) (a : Fin v)
    (h : vertexBoundCheck D available a bounds = true) :
    vertexUpper D S available a ≤ vertexBound D S bounds a := by
  apply Nat.add_le_add_left
  apply sum_map_le
  intro j hj
  exact boundCheck_sound _ _ _ (List.all_eq_true.mp h j hj)

def check (D : Problem n r e v k) (S : List (Fin n))
    (selected available : Nat) (bounds : Bounds n) (rule : Rule r e v k) : Bool :=
  match rule with
  | .kindCapacity j =>
      match bounds.getD j.val none with
      | none => false
      | some xs => boundCheck (Nat.land available (D.cache.kinds j.val)) (some xs) &&
          decide (kindCount D.kind S j.val + xs.length < D.quota j.val)
  | .vertexCapacity a =>
      vertexBoundCheck D available a bounds &&
        decide (vertexBound D S bounds a < D.minimumIncidence)
  | _ => ruleCheck D S selected available rule

theorem check_sound (D : Problem n r e v k) (S : List (Fin n))
    (selected available : Nat) (bounds : Bounds n) (rule : Rule r e v k)
    (h : check D S selected available bounds rule = true) :
    ruleCheck D S selected available rule = true := by
  cases rule with
  | ridge q owner => exact h
  | edge q => exact h
  | nonedge q possible => exact h
  | nonedgeCapacity possible => exact h
  | kindCapacity j =>
    cases hb : bounds.getD j.val none with
    | none => simp only [check, hb, Bool.false_eq_true] at h
    | some xs =>
      obtain ⟨hcover, hlt⟩ := Bool.and_eq_true_iff.mp
        (by simpa only [check, hb] using h)
      have hc := card_le_length_of_cover
        (Nat.land available (D.cache.kinds j.val)) xs (of_decide_eq_true hcover)
      have hlt := of_decide_eq_true hlt
      apply decide_eq_true
      change kindCount D.kind S j.val + card n
        (Nat.land available (D.cache.kinds j.val)) < D.quota j.val
      omega
  | vertexCapacity a =>
    obtain ⟨hb, hlt⟩ := Bool.and_eq_true_iff.mp h
    have hu := vertexBoundCheck_sound D S available bounds a hb
    have hlt := of_decide_eq_true hlt
    exact decide_eq_true (Nat.lt_of_le_of_lt hu hlt)

#print axioms check_sound

end Papers.RationalityTen.FastGraphRuleCheck
