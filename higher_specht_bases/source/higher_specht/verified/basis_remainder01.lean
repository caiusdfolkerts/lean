module

public import higher_specht.verified.basis01
public import tau_ceti.representation_theory.symmetric.row_column_subgroup
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maps
public import tau_ceti.combinatorics.young.standard_tableau.reading
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import tau_ceti.combinatorics.young.rsk

/- Generated ordinary proof stage. See audit/staged_specht_basis_batched/BasisRemainder01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/LascouxKnuthReflections.lean -/



/-!
# The constructed reflections act on actual Knuth classes

Both partial string operations preserve the literal Knuth relation, so their
finite iterates and string reflections do too.  This proves that the concrete
content-swap maps descend to insertion classes.  Preservation of each tableau's
shape, the canonical path identities, and the catabolizability image remain
separate obligations.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem OptionKnuth.bind {u v : Option (List ℕ)} {f g : List ℕ → Option (List ℕ)}
    (huv : OptionKnuth u v)
    (hfg : ∀ {x y}, KnuthEquivalent x y → OptionKnuth (f x) (g y)) :
    OptionKnuth (u.bind f) (v.bind g) := by
  cases u with
  | none => cases v <;> first | trivial | exact huv.elim
  | some x =>
      cases v with
      | none => exact huv.elim
      | some y => exact hfg huv

theorem listString_lowerIterate_of_knuth (r k : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) :
    OptionKnuth ((listString r).lowerIterate k u) ((listString r).lowerIterate k v) := by
  induction k generalizing u v with
  | zero => exact h
  | succ k ih =>
      change OptionKnuth (((listString r).lower u).bind ((listString r).lowerIterate k))
        (((listString r).lower v).bind ((listString r).lowerIterate k))
      exact (listString_lower_of_knuth r h).bind (fun hxy => ih hxy)

theorem listString_raiseIterate_of_knuth (r k : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) :
    OptionKnuth ((listString r).reverse.lowerIterate k u)
      ((listString r).reverse.lowerIterate k v) := by
  induction k generalizing u v with
  | zero => exact h
  | succ k ih =>
      change OptionKnuth (((listString r).raise u).bind ((listString r).reverse.lowerIterate k))
        (((listString r).raise v).bind ((listString r).reverse.lowerIterate k))
      exact (listString_raise_of_knuth r h).bind (fun hxy => ih hxy)

theorem listString_reflection_of_knuth (r : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) :
    KnuthEquivalent ((listString r).reflection u) ((listString r).reflection v) := by
  obtain ⟨he, hp⟩ := listString_signature_of_knuth r h
  unfold StringSystem.reflection
  by_cases hd : (listString r).epsilon u ≤ (listString r).phi u
  · have hdv : (listString r).epsilon v ≤ (listString r).phi v := by simpa [← he, ← hp] using hd
    rw [dif_pos hd, dif_pos hdv]
    have hh := listString_lowerIterate_of_knuth r
      ((listString r).phi u - (listString r).epsilon u) h
    have hv : (listString r).lowerIterate
        ((listString r).phi u - (listString r).epsilon u) v =
        some ((listString r).lowerAt
          ((listString r).phi v - (listString r).epsilon v) v (Nat.sub_le _ _)) := by
      rw [hp, he]
      exact (listString r).lowerAt_spec _ v (Nat.sub_le _ _)
    rw [(listString r).lowerAt_spec _ u (Nat.sub_le _ _), hv] at hh
    exact hh
  · have hdv : ¬ (listString r).epsilon v ≤ (listString r).phi v := by simpa [← he, ← hp] using hd
    rw [dif_neg hd, dif_neg hdv]
    have hh := listString_raiseIterate_of_knuth r
      ((listString r).epsilon u - (listString r).phi u) h
    have hv : (listString r).reverse.lowerIterate
        ((listString r).epsilon u - (listString r).phi u) v =
        some ((listString r).reverse.lowerAt
          ((listString r).epsilon v - (listString r).phi v) v
          (Nat.sub_le ((listString r).epsilon v) ((listString r).phi v))) := by
      rw [he, hp]
      exact (listString r).reverse.lowerAt_spec
        ((listString r).epsilon v - (listString r).phi v) v (Nat.sub_le _ _)
    rw [(listString r).reverse.lowerAt_spec
      ((listString r).epsilon u - (listString r).phi u) u (Nat.sub_le _ _), hv] at hh
    exact hh

theorem listString_lowerIterate_ofFn (r n k : ℕ) (u : Fin n → ℕ) :
    (listString r).lowerIterate k (List.ofFn u) =
      ((wordString r n).lowerIterate k u).map List.ofFn := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
      change ((listString r).lower (List.ofFn u)).bind ((listString r).lowerIterate k) =
        (((wordString r n).lower u).bind ((wordString r n).lowerIterate k)).map List.ofFn
      rw [listString_lower_ofFn]
      cases h : (wordString r n).lower u <;> simp [h, ih]

theorem listString_raiseIterate_ofFn (r n k : ℕ) (u : Fin n → ℕ) :
    (listString r).reverse.lowerIterate k (List.ofFn u) =
      ((wordString r n).reverse.lowerIterate k u).map List.ofFn := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
      change ((listString r).raise (List.ofFn u)).bind ((listString r).reverse.lowerIterate k) =
        (((wordString r n).raise u).bind ((wordString r n).reverse.lowerIterate k)).map List.ofFn
      rw [listString_raise_ofFn]
      cases h : (wordString r n).raise u <;> simp [h, ih]

theorem listString_reflection_ofFn (r n : ℕ) (u : Fin n → ℕ) :
    (listString r).reflection (List.ofFn u) = List.ofFn (wordReflection r n u) := by
  change (listString r).reflection (List.ofFn u) =
    List.ofFn ((wordString r n).reflection u)
  unfold StringSystem.reflection
  simp only [listString_epsilon_ofFn, listString_phi_ofFn]
  split_ifs with h
  · have ht := listString_lowerIterate_ofFn r n
      ((wordString r n).phi u - (wordString r n).epsilon u) u
    rw [(wordString r n).lowerAt_spec _ u (Nat.sub_le _ _), Option.map_some] at ht
    have hs := (listString r).lowerAt_spec
      ((wordString r n).phi u - (wordString r n).epsilon u) (List.ofFn u)
      (by simpa only [listString_phi_ofFn] using
        (Nat.sub_le ((wordString r n).phi u) ((wordString r n).epsilon u)))
    rw [ht] at hs
    exact (Option.some.inj hs).symm
  · have ht := listString_raiseIterate_ofFn r n
      ((wordString r n).epsilon u - (wordString r n).phi u) u
    rw [(wordString r n).reverse.lowerAt_spec
      ((wordString r n).epsilon u - (wordString r n).phi u) u (Nat.sub_le _ _),
      Option.map_some] at ht
    have hs := (listString r).reverse.lowerAt_spec
      ((wordString r n).epsilon u - (wordString r n).phi u) (List.ofFn u)
      (by simpa only [StringSystem.reverse_phi, listString_epsilon_ofFn] using
        (Nat.sub_le ((wordString r n).epsilon u) ((wordString r n).phi u)))
    rw [ht] at hs
    exact (Option.some.inj hs).symm

def PreservesWordKnuth {n : ℕ} (e : (Fin n → ℕ) ≃ (Fin n → ℕ)) : Prop :=
  ∀ u v, KnuthEquivalent (List.ofFn (e u)) (List.ofFn (e v)) ↔
    KnuthEquivalent (List.ofFn u) (List.ofFn v)

theorem PreservesWordKnuth.refl (n : ℕ) :
    PreservesWordKnuth (Equiv.refl (Fin n → ℕ)) := fun _ _ => Iff.rfl

theorem PreservesWordKnuth.trans {n : ℕ} {e f : (Fin n → ℕ) ≃ (Fin n → ℕ)}
    (he : PreservesWordKnuth e) (hf : PreservesWordKnuth f) :
    PreservesWordKnuth (e.trans f) := by
  intro u v
  exact (hf (e u) (e v)).trans (he u v)

theorem PreservesWordKnuth.symm {n : ℕ} {e : (Fin n → ℕ) ≃ (Fin n → ℕ)}
    (he : PreservesWordKnuth e) : PreservesWordKnuth e.symm := by
  intro u v
  simpa only [Equiv.apply_symm_apply] using (he (e.symm u) (e.symm v)).symm

theorem wordReflection_preserves_knuth (r n : ℕ) :
    PreservesWordKnuth (wordReflection r n) := by
  have hf {u v : Fin n → ℕ} (h : KnuthEquivalent (List.ofFn u) (List.ofFn v)) :
      KnuthEquivalent (List.ofFn (wordReflection r n u))
        (List.ofFn (wordReflection r n v)) := by
    simpa only [listString_reflection_ofFn] using listString_reflection_of_knuth r h
  intro u v
  constructor
  · intro h
    simpa only [wordReflection_involutive r n u, wordReflection_involutive r n v] using hf h
  · exact hf

theorem wordSwapZero_preserves_knuth (n j : ℕ) :
    PreservesWordKnuth (wordSwapZero n j) := by
  induction j using Nat.twoStepInduction with
  | zero => exact PreservesWordKnuth.refl n
  | one => exact wordReflection_preserves_knuth 0 n
  | more j ih ih' =>
      exact (wordReflection_preserves_knuth (j + 1) n).trans
        (ih'.trans (wordReflection_preserves_knuth (j + 1) n))

theorem wordContentSwap_preserves_knuth (n i j : ℕ) :
    PreservesWordKnuth (wordContentSwap n i j) := by
  unfold wordContentSwap
  split_ifs
  · exact PreservesWordKnuth.refl n
  · exact wordSwapZero_preserves_knuth n j
  · exact wordSwapZero_preserves_knuth n i
  · exact (wordSwapZero_preserves_knuth n i).trans
      ((wordSwapZero_preserves_knuth n j).trans (wordSwapZero_preserves_knuth n i))

theorem wordBringPair_preserves_knuth (n i j : ℕ) :
    PreservesWordKnuth (wordBringPair n i j) :=
  (wordContentSwap_preserves_knuth n 0 i).trans
    (wordContentSwap_preserves_knuth n 1 (Equiv.swap 0 i j))

end HigherSpecht.Lascoux
end
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/LascouxTableauReflections.lean -/



/-!
# Same-shape transport for the genuine signature reflections

Every finite raising/lowering iterate stays in the original semistandard
tableau shape.  This proves the same property for the actual string reflection
and for the explicit content transposition words.  The result concerns the
constructed operators themselves; it does not assume a Weyl-group action or
path independence.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

theorem exists_tableau_of_word_lowerIterate (T : SemistandardYoungTableau mu) (v k : ℕ)
    {output : List ℕ} (h : (listString v).lowerIterate k (tableauWord T) = some output) :
    ∃ U : SemistandardYoungTableau mu, tableauWord U = output := by
  induction k generalizing T with
  | zero => exact ⟨T, Option.some.inj h⟩
  | succ k ih =>
      obtain ⟨word, hword, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨U, hU⟩ := exists_tableau_of_word_lowering T v hword
      exact ih U (hU.symm ▸ hrest)

theorem exists_tableau_of_word_raiseIterate (T : SemistandardYoungTableau mu) (v k : ℕ)
    {output : List ℕ} (h : (listString v).reverse.lowerIterate k (tableauWord T) = some output) :
    ∃ U : SemistandardYoungTableau mu, tableauWord U = output := by
  induction k generalizing T with
  | zero => exact ⟨T, Option.some.inj h⟩
  | succ k ih =>
      obtain ⟨word, hword, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨U, hU⟩ := exists_tableau_of_word_raising T v hword
      exact ih U (hU.symm ▸ hrest)

theorem exists_tableau_of_word_reflection (T : SemistandardYoungTableau mu) (v : ℕ) :
    ∃ U : SemistandardYoungTableau mu,
      tableauWord U = (listString v).reflection (tableauWord T) := by
  unfold StringSystem.reflection
  split_ifs with h
  · exact exists_tableau_of_word_lowerIterate T v _
      ((listString v).lowerAt_spec _ (tableauWord T) (Nat.sub_le _ _))
  · exact exists_tableau_of_word_raiseIterate T v _
      ((listString v).reverse.lowerAt_spec _ (tableauWord T) (Nat.sub_le _ _))

def PreservesTableauWord {n : ℕ} (f : (Fin n → ℕ) → (Fin n → ℕ)) : Prop :=
  ∀ {mu : YoungDiagram} (T : SemistandardYoungTableau mu) (u : Fin n → ℕ),
    List.ofFn u = tableauWord T →
      ∃ U : SemistandardYoungTableau mu, List.ofFn (f u) = tableauWord U

theorem PreservesTableauWord.id (n : ℕ) :
    PreservesTableauWord (id : (Fin n → ℕ) → (Fin n → ℕ)) := by
  intro mu T u hu
  exact ⟨T, hu⟩

theorem PreservesTableauWord.comp {n : ℕ}
    {f g : (Fin n → ℕ) → (Fin n → ℕ)}
    (hf : PreservesTableauWord f) (hg : PreservesTableauWord g) :
    PreservesTableauWord (g ∘ f) := by
  intro mu T u hu
  obtain ⟨U, hU⟩ := hf T u hu
  exact hg U (f u) hU

def PreservesTableauWordEquiv {n : ℕ} (e : (Fin n → ℕ) ≃ (Fin n → ℕ)) : Prop :=
  PreservesTableauWord e ∧ PreservesTableauWord e.symm

theorem PreservesTableauWordEquiv.refl (n : ℕ) :
    PreservesTableauWordEquiv (Equiv.refl (Fin n → ℕ)) :=
  ⟨PreservesTableauWord.id n, PreservesTableauWord.id n⟩

theorem PreservesTableauWordEquiv.trans {n : ℕ}
    {e f : (Fin n → ℕ) ≃ (Fin n → ℕ)}
    (he : PreservesTableauWordEquiv e) (hf : PreservesTableauWordEquiv f) :
    PreservesTableauWordEquiv (e.trans f) := by
  constructor
  · exact PreservesTableauWord.comp he.1 hf.1
  · exact PreservesTableauWord.comp hf.2 he.2

theorem wordReflection_preserves_tableau (v n : ℕ) :
    PreservesTableauWordEquiv (wordReflection v n) := by
  have hf : PreservesTableauWord (wordReflection v n) := by
    intro mu T u hu
    obtain ⟨U, hU⟩ := exists_tableau_of_word_reflection T v
    refine ⟨U, ?_⟩
    rw [← listString_reflection_ofFn, hu]
    exact hU.symm
  refine ⟨hf, ?_⟩
  have heq : (wordReflection v n).symm = wordReflection v n := by
    apply Equiv.ext
    intro u
    apply (wordReflection v n).injective
    exact (Equiv.apply_symm_apply (wordReflection v n) u).trans
      (wordReflection_involutive v n u).symm
  rw [heq]
  intro mu T u hu
  exact hf T u hu

theorem wordSwapZero_preserves_tableau (n j : ℕ) :
    PreservesTableauWordEquiv (wordSwapZero n j) := by
  induction j using Nat.twoStepInduction with
  | zero => exact PreservesTableauWordEquiv.refl n
  | one => exact wordReflection_preserves_tableau 0 n
  | more j ih ih' =>
      exact (wordReflection_preserves_tableau (j + 1) n).trans
        (ih'.trans (wordReflection_preserves_tableau (j + 1) n))

theorem wordContentSwap_preserves_tableau (n i j : ℕ) :
    PreservesTableauWordEquiv (wordContentSwap n i j) := by
  unfold wordContentSwap
  split_ifs
  · exact PreservesTableauWordEquiv.refl n
  · exact wordSwapZero_preserves_tableau n j
  · exact wordSwapZero_preserves_tableau n i
  · exact (wordSwapZero_preserves_tableau n i).trans
      ((wordSwapZero_preserves_tableau n j).trans (wordSwapZero_preserves_tableau n i))

theorem wordBringPair_preserves_tableau (n i j : ℕ) :
    PreservesTableauWordEquiv (wordBringPair n i j) :=
  (wordContentSwap_preserves_tableau n 0 i).trans
    (wordContentSwap_preserves_tableau n 1 (Equiv.swap 0 i j))

end HigherSpecht.Lascoux
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/LascouxSaturatedReflection.lean -/



/-!
# The actual adjacent reflection at a saturated letter

If the lower letter occurs as often as the first-row width, it occurs in
every column.  The genuine signature reflection uses only lowerings in
this situation.  Its upper letter is again saturated.  Column strictness
therefore forces the exact local rule: a column containing both letters
stays fixed, and its lower letter changes to the upper letter otherwise.

This is a proved special formula for the constructed reflection, not an
assumed identification with a Bender--Knuth involution.
-/

noncomputable section

open scoped Classical

namespace HigherSpecht.Lascoux

def LowerOnly (r a b : ℕ) : Prop := b = a ∨ a = r ∧ b = r + 1

theorem LowerOnly.refl (r a : ℕ) : LowerOnly r a a := Or.inl rfl

theorem LowerOnly.trans {r a b c : ℕ}
    (hab : LowerOnly r a b) (hbc : LowerOnly r b c) : LowerOnly r a c := by
  unfold LowerOnly at *
  rcases hab with hab | ⟨ha, hb⟩ <;> rcases hbc with hbc | ⟨hb', hc⟩ <;> omega

theorem word_lowerIterate_lowerOnly (r n k : ℕ) {u v : Fin n → ℕ}
    (h : (wordString r n).lowerIterate k u = some v) :
    ∀ i, LowerOnly r (u i) (v i) := by
  induction k generalizing u with
  | zero =>
      have hu : u = v := Option.some.inj h
      subst v
      exact fun i => LowerOnly.refl r _
  | succ k ih =>
      obtain ⟨w, huw, hwv⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨j, huj, hw⟩ := wordString_lower_changes_one r n huw
      intro i
      apply LowerOnly.trans (b := w i) _ (ih hwv i)
      rw [hw]
      by_cases hij : i = j
      · subst i
        exact Or.inr ⟨huj, Function.update_self _ _ _⟩
      · exact Or.inl (Function.update_of_ne hij _ _)

theorem wordReflection_lowerOnly_of_count_ge (r n : ℕ) (u : Fin n → ℕ)
    (hc : (List.ofFn u).count (r + 1) ≤ (List.ofFn u).count r) :
    ∀ i, LowerOnly r (u i) (wordReflection r n u i) := by
  have hb := wordString_balance r n u
  have hdir : (wordString r n).epsilon u ≤ (wordString r n).phi u := by omega
  change ∀ i, LowerOnly r (u i) ((wordString r n).reflection u i)
  rw [StringSystem.reflection, dif_pos hdir]
  exact word_lowerIterate_lowerOnly r n _ ((wordString r n).lowerAt_spec _ u (Nat.sub_le _ _))

theorem forall₂_ofFn_of_forall {A B : Type*} (rel : A → B → Prop)
    (n : ℕ) (f : Fin n → A) (g : Fin n → B) (h : ∀ i, rel (f i) (g i)) :
    List.Forall₂ rel (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons (h 0) (ih (Fin.tail f) (Fin.tail g) (fun i => h i.succ))

theorem forall₂_map_same_list_iff {A B C : Type*} (rel : B → C → Prop)
    (xs : List A) (f : A → B) (g : A → C) :
    List.Forall₂ rel (xs.map f) (xs.map g) ↔ ∀ x ∈ xs, rel (f x) (g x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.forall₂_cons, List.mem_cons,
        forall_eq_or_imp, ih]

theorem listString_reflection_lowerOnly_of_count_ge (r : ℕ) (w : List ℕ)
    (hc : w.count (r + 1) ≤ w.count r) :
    List.Forall₂ (LowerOnly r) w ((listString r).reflection w) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change (List.ofFn u).count (r + 1) ≤ (List.ofFn u).count r at hc
  change List.Forall₂ (LowerOnly r) (List.ofFn u)
    ((listString r).reflection (List.ofFn u))
  rw [listString_reflection_ofFn]
  exact forall₂_ofFn_of_forall (LowerOnly r) n u (wordReflection r n u)
    (wordReflection_lowerOnly_of_count_ge r n u hc)

theorem listString_reflection_count (r a : ℕ) (w : List ℕ) :
    ((listString r).reflection w).count a =
      if a = r then w.count (r + 1)
      else if a = r + 1 then w.count r else w.count a := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change ((listString r).reflection (List.ofFn u)).count a =
    if a = r then (List.ofFn u).count (r + 1)
    else if a = r + 1 then (List.ofFn u).count r else (List.ofFn u).count a
  rw [listString_reflection_ofFn]
  exact wordReflection_count r n a u

variable {mu : YoungDiagram}

/-- When the actual word reflection only lowers, its same-shape tableau
representative changes precisely those same cell positions. -/
theorem reflectedTableau_lowerOnly (T U : SemistandardYoungTableau mu) (r : ℕ)
    (hc : (tableauWord T).count (r + 1) ≤ (tableauWord T).count r)
    (hU : tableauWord U = (listString r).reflection (tableauWord T)) :
    ∀ i j, LowerOnly r (T i j) (U i j) := by
  have hw := listString_reflection_lowerOnly_of_count_ge r (tableauWord T) hc
  rw [← hU, tableauWord_eq_map_cells, tableauWord_eq_map_cells] at hw
  have hcells := (forall₂_map_same_list_iff (LowerOnly r) (tableauCellReading mu)
    (fun c => T c.1 c.2) (fun c => U c.1 c.2)).mp hw
  intro i j
  by_cases hij : (i, j) ∈ mu
  · exact hcells (i, j) ((mem_tableauCellReading mu (i, j)).mpr hij)
  · rw [T.zeros hij, U.zeros hij]
    exact LowerOnly.refl r 0

theorem reflectedTableau_upper_saturated (T U : SemistandardYoungTableau mu) (r : ℕ)
    (hc : (contentCells T r).card = mu.rowLen 0)
    (hU : tableauWord U = (listString r).reflection (tableauWord T)) :
    (contentCells U (r + 1)).card = mu.rowLen 0 := by
  rw [← tableauWord_count_eq_contentCells, hU, listString_reflection_count]
  simp only [show r + 1 ≠ r by omega, if_false, if_pos rfl]
  rw [tableauWord_count_eq_contentCells]
  exact hc

/-- The exact cell formula for an actual signature reflection at a
saturated lower letter.  Every occurrence of the upper letter is fixed;
the unique lower letter in its column is fixed precisely when paired with
such an upper letter in that same column. -/
theorem reflectedTableau_saturated_entry (T U : SemistandardYoungTableau mu) (r : ℕ)
    (hc : (contentCells T r).card = mu.rowLen 0)
    (hU : tableauWord U = (listString r).reflection (tableauWord T))
    (i j : ℕ) (hij : (i, j) ∈ mu) :
    U i j = if T i j = r ∧ ¬∃ s, (s, j) ∈ mu ∧ T s j = r + 1
      then r + 1 else T i j := by
  have hcount : (tableauWord T).count (r + 1) ≤ (tableauWord T).count r := by
    rw [tableauWord_count_eq_contentCells, tableauWord_count_eq_contentCells, hc]
    exact contentCells_card_le_width T (r + 1)
  have hlocal := reflectedTableau_lowerOnly T U r hcount hU
  by_cases hTi : T i j = r
  · by_cases hpair : ∃ s, (s, j) ∈ mu ∧ T s j = r + 1
    · rw [if_neg (fun h => h.2 hpair)]
      rcases hlocal i j with hsame | ⟨_, hnew⟩
      · exact hsame
      · obtain ⟨s, hsj, hTs⟩ := hpair
        have hUs : U s j = r + 1 := by
          rcases hlocal s j with heq | ⟨hbad, _⟩
          · exact heq.trans hTs
          · omega
        have heq := contentCells_column_injective U (r + 1)
          (Finset.mem_filter.mpr ⟨hij, hnew⟩)
          (Finset.mem_filter.mpr ⟨hsj, hUs⟩) rfl
        have his : i = s := congrArg Prod.fst heq
        rw [← his, hTi] at hTs
        omega
    · rw [if_pos ⟨hTi, hpair⟩]
      have hj : j < mu.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
        (mu.up_left_mem (Nat.zero_le i) le_rfl hij)
      obtain ⟨s, ⟨hsj, hUs⟩, _⟩ := existsUnique_entry_in_each_column U (r + 1)
        (reflectedTableau_upper_saturated T U r hc hU) j hj
      have hTs : T s j = r := by
        rcases hlocal s j with heq | ⟨hlow, _⟩
        · exact (hpair ⟨s, hsj, heq.symm.trans hUs⟩).elim
        · exact hlow
      have heq := contentCells_column_injective T r
        (Finset.mem_filter.mpr ⟨hsj, hTs⟩)
        (Finset.mem_filter.mpr ⟨hij, hTi⟩) rfl
      have hsi : s = i := congrArg Prod.fst heq
      simpa only [hsi] using hUs
  · rw [if_neg (fun h => hTi h.1)]
    rcases hlocal i j with heq | ⟨hlow, _⟩
    · exact heq
    · exact (hTi hlow).elim

def signatureReflectionTableau (T : SemistandardYoungTableau mu) (r : ℕ) :
    SemistandardYoungTableau mu :=
  Classical.choose (exists_tableau_of_word_reflection T r)

@[simp] theorem signatureReflectionTableau_word (T : SemistandardYoungTableau mu) (r : ℕ) :
    tableauWord (signatureReflectionTableau T r) =
      (listString r).reflection (tableauWord T) :=
  Classical.choose_spec (exists_tableau_of_word_reflection T r)

theorem signatureReflectionTableau_saturated_entry
    (T : SemistandardYoungTableau mu) (r : ℕ)
    (hc : (contentCells T r).card = mu.rowLen 0)
    (i j : ℕ) (hij : (i, j) ∈ mu) :
    signatureReflectionTableau T r i j =
      if T i j = r ∧ ¬∃ s, (s, j) ∈ mu ∧ T s j = r + 1
      then r + 1 else T i j :=
  reflectedTableau_saturated_entry T (signatureReflectionTableau T r) r hc
    (signatureReflectionTableau_word T r) i j hij

theorem signatureReflectionTableau_upper_saturated
    (T : SemistandardYoungTableau mu) (r : ℕ)
    (hc : (contentCells T r).card = mu.rowLen 0) :
    (contentCells (signatureReflectionTableau T r) (r + 1)).card = mu.rowLen 0 :=
  reflectedTableau_upper_saturated T (signatureReflectionTableau T r) r hc
    (signatureReflectionTableau_word T r)

end HigherSpecht.Lascoux
end
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/LascouxSaturatedSweep.lean -/



/-!
# An explicit sweep of a saturated letter through the alphabet

The operators are the actual adjacent signature reflections in the order
`0, 1, ..., M-1`.  Starting with a zero in every column, their effect on
each column is the cycle of its alphabet `0 ↦ M`, `a ↦ a-1` for `0<a≤M`.
The columns remain strictly increasing, so sorting this literal content
identity puts the original nonzero entries, decreased by one, above a
final `M`.  This is the precise recursive base transformation; no path
independence or catabolism-image theorem is assumed.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

def HasColumnValue (T : SemistandardYoungTableau mu) (j a : ℕ) : Prop :=
  ∃ i, (i, j) ∈ mu ∧ T i j = a

theorem not_hasColumnValue_of_width_le (T : SemistandardYoungTableau mu)
    {j a : ℕ} (hj : mu.rowLen 0 ≤ j) : ¬HasColumnValue T j a := by
  rintro ⟨i, hij, _⟩
  have h := YoungDiagram.mem_iff_lt_rowLen.mp
    (mu.up_left_mem (Nat.zero_le i) le_rfl hij)
  omega

theorem saturated_hasColumnValue (T : SemistandardYoungTableau mu) (a : ℕ)
    (hs : (contentCells T a).card = mu.rowLen 0) {j : ℕ} (hj : j < mu.rowLen 0) :
    HasColumnValue T j a := by
  obtain ⟨i, hi, _⟩ := existsUnique_entry_in_each_column T a hs j hj
  exact ⟨i, hi⟩

/-- On each literal column the saturated adjacent reflection is exactly
the transposition of the two adjacent alphabet values. -/
theorem signatureReflectionTableau_column_values
    (T : SemistandardYoungTableau mu) (r : ℕ)
    (hs : (contentCells T r).card = mu.rowLen 0) (j a : ℕ) :
    HasColumnValue (signatureReflectionTableau T r) j a ↔
      HasColumnValue T j (Equiv.swap r (r + 1) a) := by
  let U := signatureReflectionTableau T r
  have hu : (contentCells U (r + 1)).card = mu.rowLen 0 :=
    signatureReflectionTableau_upper_saturated T r hs
  have hf (i : ℕ) (hij : (i, j) ∈ mu) :
      U i j = if T i j = r ∧ ¬HasColumnValue T j (r + 1)
        then r + 1 else T i j :=
    signatureReflectionTableau_saturated_entry T r hs i j hij
  by_cases hj : j < mu.rowLen 0
  · have hr := saturated_hasColumnValue T r hs hj
    have hr' := saturated_hasColumnValue U (r + 1) hu hj
    by_cases har : a = r
    · subst a
      rw [Equiv.swap_apply_left]
      constructor
      · rintro ⟨i, hij, hui⟩
        by_contra hn
        have hfi := hf i hij
        by_cases hTi : T i j = r
        · rw [if_pos ⟨hTi, hn⟩] at hfi
          change U i j = r + 1 at hfi
          have hbad : r = r + 1 := hui.symm.trans hfi
          omega
        · rw [if_neg (by tauto)] at hfi
          exact hTi (hfi.symm.trans hui)
      · intro hp
        obtain ⟨i, hij, hTi⟩ := hr
        refine ⟨i, hij, ?_⟩
        have hfi := hf i hij
        rw [if_neg (by tauto), hTi] at hfi
        exact hfi
    · by_cases har' : a = r + 1
      · subst a
        rw [Equiv.swap_apply_right]
        exact ⟨fun _ => hr, fun _ => hr'⟩
      · rw [Equiv.swap_apply_of_ne_of_ne har har']
        constructor
        · rintro ⟨i, hij, hui⟩
          have hfi := hf i hij
          by_cases hc : T i j = r ∧ ¬HasColumnValue T j (r + 1)
          · rw [if_pos hc] at hfi
            exact (har' (hui.symm.trans hfi)).elim
          · rw [if_neg hc] at hfi
            exact ⟨i, hij, hfi.symm.trans hui⟩
        · rintro ⟨i, hij, hTi⟩
          refine ⟨i, hij, ?_⟩
          have hfi := hf i hij
          rw [if_neg (by intro h; exact har (hTi.symm.trans h.1))] at hfi
          exact hfi.trans hTi
  · have hj' : mu.rowLen 0 ≤ j := Nat.le_of_not_gt hj
    exact ⟨fun h => (not_hasColumnValue_of_width_le U hj' h).elim,
      fun h => (not_hasColumnValue_of_width_le T hj' h).elim⟩

def alphabetSweep : ℕ → Equiv.Perm ℕ
  | 0 => Equiv.refl ℕ
  | k + 1 => (alphabetSweep k).trans (Equiv.swap k (k + 1))

@[simp] theorem alphabetSweep_zero (k : ℕ) : alphabetSweep k 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [alphabetSweep, Equiv.trans_apply, ih, Equiv.swap_apply_left]

theorem alphabetSweep_of_gt {k a : ℕ} (hka : k < a) : alphabetSweep k a = a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [alphabetSweep, Equiv.trans_apply, ih (by omega)]
      exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

theorem alphabetSweep_of_pos_le {k a : ℕ} (ha : 0 < a) (hak : a ≤ k) :
    alphabetSweep k a = a - 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [alphabetSweep, Equiv.trans_apply]
      by_cases hak' : a ≤ k
      · rw [ih hak']
        exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
      · have ha' : a = k + 1 := by omega
        subst a
        rw [alphabetSweep_of_gt (by omega), Equiv.swap_apply_right]
        omega

def saturatedSweep (T : SemistandardYoungTableau mu) : ℕ → SemistandardYoungTableau mu
  | 0 => T
  | k + 1 => signatureReflectionTableau (saturatedSweep T k) k

def wordReflectionSweep : ℕ → List ℕ → List ℕ
  | 0, w => w
  | k + 1, w => (listString k).reflection (wordReflectionSweep k w)

theorem saturatedSweep_word (T : SemistandardYoungTableau mu) (k : ℕ) :
    tableauWord (saturatedSweep T k) = wordReflectionSweep k (tableauWord T) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [saturatedSweep, signatureReflectionTableau_word, ih]
      rfl

theorem saturatedSweep_saturated (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (k : ℕ) :
    (contentCells (saturatedSweep T k) k).card = mu.rowLen 0 := by
  induction k with
  | zero => exact hs
  | succ k ih => exact signatureReflectionTableau_upper_saturated (saturatedSweep T k) k ih

theorem saturatedSweep_column_values (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (k j a : ℕ) :
    HasColumnValue (saturatedSweep T k) j a ↔
      HasColumnValue T j ((alphabetSweep k).symm a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      rw [saturatedSweep, signatureReflectionTableau_column_values
        (saturatedSweep T k) k (saturatedSweep_saturated T hs k), ih]
      rfl

def tableauColumn (T : SemistandardYoungTableau mu) (j : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (mu.colLen j) => T i.val j)

@[simp] theorem tableauColumn_length (T : SemistandardYoungTableau mu) (j : ℕ) :
    (tableauColumn T j).length = mu.colLen j := List.length_ofFn

@[simp] theorem tableauColumn_getElem (T : SemistandardYoungTableau mu)
    (j i : ℕ) (hi : i < (tableauColumn T j).length) :
    (tableauColumn T j)[i] = T i j := by simp only [tableauColumn, List.getElem_ofFn]

theorem tableauColumn_sortedLT (T : SemistandardYoungTableau mu) (j : ℕ) :
    (tableauColumn T j).SortedLT := by
  apply List.sortedLT_ofFn_iff.mpr
  intro i k hik
  exact T.col_strict hik (YoungDiagram.mem_iff_lt_colLen.mpr k.isLt)

theorem mem_tableauColumn (T : SemistandardYoungTableau mu) (j a : ℕ) :
    a ∈ tableauColumn T j ↔ HasColumnValue T j a := by
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
    exact ⟨i.val, YoungDiagram.mem_iff_lt_colLen.mpr i.isLt, hi⟩
  · rintro ⟨i, hij, hia⟩
    exact List.mem_ofFn.mpr ⟨⟨i, YoungDiagram.mem_iff_lt_colLen.mp hij⟩, hia⟩

theorem saturatedSweep_column_perm (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (k j : ℕ) :
    (tableauColumn (saturatedSweep T k) j).Perm
      ((tableauColumn T j).map (alphabetSweep k)) := by
  apply (List.perm_ext_iff_of_nodup (tableauColumn_sortedLT _ _).nodup
    ((tableauColumn_sortedLT T j).nodup.map (alphabetSweep k).injective)).mpr
  intro a
  rw [mem_tableauColumn, saturatedSweep_column_values T hs k j a]
  constructor
  · intro ha
    exact List.mem_map.mpr ⟨(alphabetSweep k).symm a,
      (mem_tableauColumn T j _).mpr ha, (alphabetSweep k).apply_symm_apply a⟩
  · intro ha
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
    rw [← hba, Equiv.symm_apply_apply]
    exact (mem_tableauColumn T j b).mp hb

theorem tableauColumn_zero_cons (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) {j : ℕ} (hj : j < mu.rowLen 0) :
    tableauColumn T j = 0 :: (tableauColumn T j).tail := by
  obtain ⟨r, ⟨hrj, hr0⟩⟩ := saturated_hasColumnValue T 0 hs hj
  have hr := zero_cell_row hrj hr0
  subst r
  have hlen : 0 < (tableauColumn T j).length := by
    rw [tableauColumn_length]
    exact YoungDiagram.mem_iff_lt_colLen.mp hrj
  have hfirst := tableauColumn_getElem T j 0 hlen
  rw [hr0] at hfirst
  cases hcol : tableauColumn T j with
  | nil => simp [hcol] at hlen
  | cons a col =>
      simp only [hcol, List.getElem_cons_zero] at hfirst
      subst a
      rfl

/-- The entire literal column after the actual sweep, in English
top-to-bottom order.  Its final maximal letter is at the bottom. -/
theorem saturatedSweep_column_eq (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (M : ℕ)
    (hbound : ∀ i j, (i, j) ∈ mu → T i j ≤ M)
    (j : ℕ) (hj : j < mu.rowLen 0) :
    tableauColumn (saturatedSweep T M) j =
      (tableauColumn T j).tail.map (fun a => a - 1) ++ [M] := by
  have hzero := tableauColumn_zero_cons T hs hj
  have htailPos : ∀ a ∈ (tableauColumn T j).tail, 0 < a := by
    have hs' := tableauColumn_sortedLT T j
    rw [hzero, List.sortedLT_cons] at hs'
    exact hs'.1
  have htailBound : ∀ a ∈ (tableauColumn T j).tail, a ≤ M := by
    intro a ha
    have hm : a ∈ tableauColumn T j := (List.tail_sublist _).subset ha
    obtain ⟨i, hij, hia⟩ := (mem_tableauColumn T j a).mp hm
    simpa only [hia] using hbound i j hij
  have hmap : (tableauColumn T j).map (alphabetSweep M) =
      M :: (tableauColumn T j).tail.map (fun a => a - 1) := by
    conv_lhs => rw [hzero]
    rw [List.map_cons, alphabetSweep_zero]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact alphabetSweep_of_pos_le (htailPos a ha) (htailBound a ha)
  have hp := saturatedSweep_column_perm T hs M j
  rw [hmap] at hp
  have hp' : (tableauColumn (saturatedSweep T M) j).Perm
      ((tableauColumn T j).tail.map (fun a => a - 1) ++ [M]) :=
    hp.trans (List.perm_append_singleton M
      ((tableauColumn T j).tail.map (fun a => a - 1))).symm
  have hsTail : ((tableauColumn T j).tail.map (fun a => a - 1)).SortedLE := by
    apply List.sortedLE_iff_pairwise.mpr
    apply List.pairwise_map.mpr
    exact ((tableauColumn_sortedLT T j).sortedLE.pairwise.sublist
      (List.tail_sublist _)).imp (fun h => Nat.sub_le_sub_right h 1)
  apply List.Perm.eq_of_sortedLE (tableauColumn_sortedLT _ _).sortedLE _ hp'
  apply List.sortedLE_append.mpr
  refine ⟨hsTail, List.sortedLE_cons.mpr ⟨by simp, List.sortedLE_nil⟩, ?_⟩
  intro a ha b hb
  have hb' : b = M := List.mem_singleton.mp hb
  subst b
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact (Nat.sub_le _ _).trans (htailBound c hc)

/-- The cellwise version of the sweep, with the boundary condition stated
as actual membership of the next cell in the same original column. -/
theorem saturatedSweep_entry (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (M : ℕ)
    (hbound : ∀ i j, (i, j) ∈ mu → T i j ≤ M)
    (i j : ℕ) (hij : (i, j) ∈ mu) :
    saturatedSweep T M i j = if (i + 1, j) ∈ mu then T (i + 1) j - 1 else M := by
  have hj : j < mu.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
    (mu.up_left_mem (Nat.zero_le i) le_rfl hij)
  have hi : i < mu.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hij
  have hc := saturatedSweep_column_eq T hs M hbound j hj
  have hget := congrArg (fun col : List ℕ => col[i]?) hc
  rw [List.getElem?_eq_getElem (by simpa only [tableauColumn_length] using hi),
    tableauColumn_getElem] at hget
  by_cases hn : (i + 1, j) ∈ mu
  · have hi' : i < ((tableauColumn T j).tail.map (fun a => a - 1)).length := by
      simp only [List.length_map, List.length_tail, tableauColumn_length]
      have hn' := YoungDiagram.mem_iff_lt_colLen.mp hn
      omega
    rw [List.getElem?_append_left hi', List.getElem?_eq_getElem hi',
      List.getElem_map, List.getElem_tail, tableauColumn_getElem] at hget
    simpa only [if_pos hn] using Option.some.inj hget
  · have hi' : i = ((tableauColumn T j).tail.map (fun a => a - 1)).length := by
      simp only [List.length_map, List.length_tail, tableauColumn_length]
      have hn' : ¬i + 1 < mu.colLen j := by
        simpa only [YoungDiagram.mem_iff_lt_colLen] using hn
      omega
    rw [List.getElem?_append_right (by omega), ← hi', Nat.sub_self,
      List.getElem?_cons_zero] at hget
    simpa only [if_neg hn] using Option.some.inj hget

end HigherSpecht.Lascoux
end
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/LascouxSweepTail.lean -/



/-!
# The actual recursive tableau after a saturated alphabet sweep

The shape is obtained by deleting the original first row.  Its tableau is
the remaining original entries, all decreased by one.  Restricting the
actual saturated sweep to letters below the final maximal letter gives
exactly this tableau, including equality of its shape.  Empty shapes and
an alphabet consisting only of zero are included.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

def firstRowTail (mu : YoungDiagram) : YoungDiagram where
  cells := mu.cells.filter (fun c => (c.1 + 1, c.2) ∈ mu)
  isLowerSet := by
    intro a b hab hb
    obtain ⟨hbm, hbs⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨mu.isLowerSet hab hbm,
      mu.up_left_mem (Nat.add_le_add_right hab.1 1) hab.2 hbs⟩

@[simp] theorem mem_firstRowTail (mu : YoungDiagram) (i j : ℕ) :
    (i, j) ∈ firstRowTail mu ↔ (i + 1, j) ∈ mu := by
  change (i, j) ∈ mu.cells.filter (fun c => (c.1 + 1, c.2) ∈ mu) ↔ _
  rw [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨mu.up_left_mem (by omega) le_rfl h, h⟩⟩

@[simp] theorem firstRowTail_rowLen (mu : YoungDiagram) (i : ℕ) :
    (firstRowTail mu).rowLen i = mu.rowLen (i + 1) := by
  have h (j : ℕ) : j < (firstRowTail mu).rowLen i ↔ j < mu.rowLen (i + 1) := by
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_firstRowTail,
      YoungDiagram.mem_iff_lt_rowLen]
  have h₁ := h ((firstRowTail mu).rowLen i)
  have h₂ := h (mu.rowLen (i + 1))
  omega

@[simp] theorem firstRowTail_colLen (mu : YoungDiagram) (j : ℕ) :
    (firstRowTail mu).colLen j = mu.colLen j - 1 := by
  have h (i : ℕ) : i < (firstRowTail mu).colLen j ↔ i + 1 < mu.colLen j := by
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_firstRowTail,
      YoungDiagram.mem_iff_lt_colLen]
  have h₁ := h ((firstRowTail mu).colLen j)
  have h₂ := h (mu.colLen j - 1)
  omega

theorem firstRowTail_card_add_width (mu : YoungDiagram) :
    (firstRowTail mu).card + mu.rowLen 0 = mu.card := by
  have htail : (firstRowTail mu).cells.card =
      (mu.cells.filter (fun c => c.1 ≠ 0)).card := by
    apply Finset.card_bij (fun c _ => (c.1 + 1, c.2))
    · intro c hc
      exact Finset.mem_filter.mpr ⟨(mem_firstRowTail mu c.1 c.2).mp hc, by omega⟩
    · intro a ha b hb hab
      have h₁ := congrArg Prod.fst hab
      have h₂ := congrArg Prod.snd hab
      exact Prod.ext (by omega) h₂
    · intro c hc
      obtain ⟨hcm, hc0⟩ := Finset.mem_filter.mp hc
      have hc1 : c.1 - 1 + 1 = c.1 := by omega
      refine ⟨(c.1 - 1, c.2), ?_, Prod.ext hc1 rfl⟩
      exact (mem_firstRowTail mu _ _).mpr (by
        simpa only [hc1, YoungDiagram.mem_cells, Prod.eta] using hcm)
  have hfirst : mu.cells.filter (fun c => c.1 = 0) =
      (Finset.range (mu.rowLen 0)).image (fun j => (0, j)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨hc, hc0⟩
      exact ⟨j, by simpa only [hc0] using YoungDiagram.mem_iff_lt_rowLen.mp hc,
        hc0.symm, rfl⟩
    · rintro ⟨k, hk, h0, hkj⟩
      subst k
      exact ⟨by simpa only [← h0] using
        (YoungDiagram.mem_iff_lt_rowLen.mpr hk : (0, j) ∈ mu), h0.symm⟩
  have hfirstCard : (mu.cells.filter (fun c => c.1 = 0)).card = mu.rowLen 0 := by
    rw [hfirst, Finset.card_image_of_injective _ (by
      intro a b hab
      exact congrArg Prod.snd hab), Finset.card_range]
  have h := Finset.card_filter_add_card_filter_not (s := mu.cells)
    (fun c : ℕ × ℕ => c.1 = 0)
  rw [hfirstCard, ← htail] at h
  change (firstRowTail mu).cells.card + mu.rowLen 0 = mu.cells.card
  omega

/-- The original first row is deleted and every remaining entry is
decreased by one.  Strict columns guarantee positivity before subtraction. -/
def firstRowTailPred (T : SemistandardYoungTableau mu) :
    SemistandardYoungTableau (firstRowTail mu) where
  entry i j := T (i + 1) j - 1
  row_weak' {i j k} hj hk :=
    Nat.sub_le_sub_right (T.row_weak hj ((mem_firstRowTail mu i k).mp hk)) 1
  col_strict' {i k j} hik hkj := by
    have hc : (k + 1, j) ∈ mu := (mem_firstRowTail mu k j).mp hkj
    have hlt : T (i + 1) j < T (k + 1) j :=
      T.col_strict (Nat.add_lt_add_right hik 1) hc
    have hi : (i + 1, j) ∈ mu :=
      mu.up_left_mem (by omega : i + 1 ≤ k + 1) le_rfl hc
    have hp : T 0 j < T (i + 1) j := T.col_strict (by omega : 0 < i + 1) hi
    omega
  zeros' {i j} hc := by
    have hn : (i + 1, j) ∉ mu := by simpa only [mem_firstRowTail] using hc
    rw [T.zeros hn]

@[simp] theorem firstRowTailPred_apply (T : SemistandardYoungTableau mu) (i j : ℕ) :
    firstRowTailPred T i j = T (i + 1) j - 1 := rfl

theorem saturated_zero_firstRow (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) {j : ℕ} (hj : j < mu.rowLen 0) :
    T 0 j = 0 := by
  obtain ⟨i, hij, hi0⟩ := saturated_hasColumnValue T 0 hs hj
  have hi := zero_cell_row hij hi0
  simpa only [hi] using hi0

theorem firstRowTailPred_content (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (a : ℕ) :
    (contentCells (firstRowTailPred T) a).card = (contentCells T (a + 1)).card := by
  apply Finset.card_bij (fun c _ => (c.1 + 1, c.2))
  · intro c hc
    obtain ⟨hcm, hca⟩ := Finset.mem_filter.mp hc
    have hcm' := (mem_firstRowTail mu c.1 c.2).mp hcm
    have hp : T 0 c.2 < T (c.1 + 1) c.2 :=
      T.col_strict (by omega : 0 < c.1 + 1) hcm'
    change T (c.1 + 1) c.2 - 1 = a at hca
    refine Finset.mem_filter.mpr ⟨hcm', ?_⟩
    change T (c.1 + 1) c.2 = a + 1
    omega
  · intro c hc d hd hcd
    have h₁ := congrArg Prod.fst hcd
    have h₂ := congrArg Prod.snd hcd
    exact Prod.ext (by omega) h₂
  · intro c hc
    obtain ⟨hcm, hca⟩ := Finset.mem_filter.mp hc
    have hc0 : c.1 ≠ 0 := by
      intro h0
      have hj : c.2 < mu.rowLen 0 := by
        simpa only [h0] using YoungDiagram.mem_iff_lt_rowLen.mp hcm
      have hz := saturated_zero_firstRow T hs hj
      have hcval : T 0 c.2 = a + 1 := by simpa only [h0] using hca
      omega
    have hpred : c.1 - 1 + 1 = c.1 := by omega
    refine ⟨(c.1 - 1, c.2), Finset.mem_filter.mpr ⟨?_, ?_⟩,
      Prod.ext hpred rfl⟩
    · exact (mem_firstRowTail mu _ _).mpr (by
        simpa only [hpred, YoungDiagram.mem_cells, Prod.eta] using hcm)
    · simp only [firstRowTailPred_apply, hpred, hca, Nat.add_sub_cancel]

/-- Restriction to an initial interval of alphabet values is an actual
Young diagram, using the original row and column orders. -/
def alphabetRestrictionShape (T : SemistandardYoungTableau mu) (M : ℕ) : YoungDiagram where
  cells := mu.cells.filter (fun c => T c.1 c.2 < M)
  isLowerSet := by
    intro a b hab hb
    obtain ⟨hbm, hbM⟩ := Finset.mem_filter.mp hb
    have hrow := T.row_weak_of_le hab.2 hbm
    have hcol := T.col_weak hab.1 (mu.up_left_mem le_rfl hab.2 hbm)
    exact Finset.mem_filter.mpr ⟨mu.isLowerSet hab hbm, lt_of_le_of_lt
      (hcol.trans hrow) hbM⟩

@[simp] theorem mem_alphabetRestrictionShape (T : SemistandardYoungTableau mu)
    (M i j : ℕ) :
    (i, j) ∈ alphabetRestrictionShape T M ↔ (i, j) ∈ mu ∧ T i j < M :=
  Finset.mem_filter

def alphabetRestriction (T : SemistandardYoungTableau mu) (M : ℕ) :
    SemistandardYoungTableau (alphabetRestrictionShape T M) where
  entry i j := if (i, j) ∈ alphabetRestrictionShape T M then T i j else 0
  row_weak' {i j k} hj hk := by
    have hc := (alphabetRestrictionShape T M).up_left_mem le_rfl hj.le hk
    simp only [if_pos hc, if_pos hk]
    exact T.row_weak hj ((mem_alphabetRestrictionShape T M i k).mp hk).1
  col_strict' {i k j} hik hk := by
    have hc := (alphabetRestrictionShape T M).up_left_mem hik.le le_rfl hk
    simp only [if_pos hc, if_pos hk]
    exact T.col_strict hik ((mem_alphabetRestrictionShape T M k j).mp hk).1
  zeros' hc := if_neg hc

@[simp] theorem alphabetRestriction_apply (T : SemistandardYoungTableau mu)
    (M i j : ℕ) :
    alphabetRestriction T M i j =
      if (i, j) ∈ alphabetRestrictionShape T M then T i j else 0 := rfl

theorem saturatedSweep_restrictionShape (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (M : ℕ)
    (hbound : ∀ i j, (i, j) ∈ mu → T i j ≤ M) :
    alphabetRestrictionShape (saturatedSweep T M) M = firstRowTail mu := by
  apply SetLike.ext
  intro c
  rcases c with ⟨i, j⟩
  rw [mem_alphabetRestrictionShape, mem_firstRowTail]
  constructor
  · rintro ⟨hc, hv⟩
    by_contra hn
    rw [saturatedSweep_entry T hs M hbound i j hc, if_neg hn] at hv
    exact (Nat.lt_irrefl M) hv
  · intro hn
    have hc := mu.up_left_mem (by omega : i ≤ i + 1) le_rfl hn
    refine ⟨hc, ?_⟩
    rw [saturatedSweep_entry T hs M hbound i j hc, if_pos hn]
    have hp := T.col_strict (by omega : 0 < i + 1) hn
    have hb := hbound (i + 1) j hn
    omega

theorem saturatedSweep_restriction_entry (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (M : ℕ)
    (hbound : ∀ i j, (i, j) ∈ mu → T i j ≤ M) (i j : ℕ) :
    alphabetRestriction (saturatedSweep T M) M i j = firstRowTailPred T i j := by
  have hshape := saturatedSweep_restrictionShape T hs M hbound
  by_cases hc : (i, j) ∈ firstRowTail mu
  · have hcs : (i, j) ∈ alphabetRestrictionShape (saturatedSweep T M) M := by
      simpa only [hshape] using hc
    have hn := (mem_firstRowTail mu i j).mp hc
    have hcm := mu.up_left_mem (by omega : i ≤ i + 1) le_rfl hn
    rw [alphabetRestriction_apply, if_pos hcs,
      saturatedSweep_entry T hs M hbound i j hcm, if_pos hn,
      firstRowTailPred_apply]
  · rw [(firstRowTailPred T).zeros hc,
      (alphabetRestriction (saturatedSweep T M) M).zeros (by simpa only [hshape] using hc)]

/-- Exact equality of both the recursive shape and the actual tableau.
The heterogeneous equality merely accounts for the initially different
syntactic expressions for the two proved-equal shapes. -/
theorem saturatedSweep_restriction (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (M : ℕ)
    (hbound : ∀ i j, (i, j) ∈ mu → T i j ≤ M) :
    alphabetRestrictionShape (saturatedSweep T M) M = firstRowTail mu ∧
      HEq (alphabetRestriction (saturatedSweep T M) M) (firstRowTailPred T) := by
  have hshape := saturatedSweep_restrictionShape T hs M hbound
  refine ⟨hshape, ?_⟩
  have aux {eta theta : YoungDiagram} (V : SemistandardYoungTableau eta)
      (W : SemistandardYoungTableau theta) (he : eta = theta)
      (hv : ∀ i j, V i j = W i j) : HEq V W := by
    subst theta
    exact heq_of_eq (SemistandardYoungTableau.ext hv)
  exact aux _ _ hshape (saturatedSweep_restriction_entry T hs M hbound)

end HigherSpecht.Lascoux
end
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/LascouxTensorReflection.lean -/



/-!
# Exact rank-one tensor reflection calculations

The lower-iterate calculation records precisely how many steps occur in each
factor: first the available excess in the first factor, then the second
factor.  At the full reflection length these two step counts are symmetric
under exchanging the factors.  This is the local algebra behind cyclic
rotation of signature words; it is separate from tableau catabolism.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux.StringSystem

variable {A B : Type*}

theorem lowerAt_succ_step (c : StringSystem A) (x : A) (k : ℕ)
    (hk : k ≤ c.phi x) (hks : k + 1 ≤ c.phi x) :
    c.lower (c.lowerAt k x hk) = some (c.lowerAt (k + 1) x hks) := by
  have h := c.lowerAt_spec (k + 1) x hks
  change partialIterate c.lower (k + 1) x = _ at h
  rw [partialIterate_succ_last] at h
  change (c.lowerIterate k x).bind c.lower = _ at h
  rw [c.lowerAt_spec k x hk, Option.bind_some] at h
  exact h

def tensorFirstSteps (c : StringSystem A) (d : StringSystem B) (x : A) (y : B) (k : ℕ) : ℕ :=
  min k (c.phi x - d.epsilon y)

def tensorSecondSteps (c : StringSystem A) (d : StringSystem B) (x : A) (y : B) (k : ℕ) : ℕ :=
  k - tensorFirstSteps c d x y k

theorem tensorFirstSteps_le (c : StringSystem A) (d : StringSystem B) (x : A) (y : B) (k : ℕ) :
    tensorFirstSteps c d x y k ≤ c.phi x :=
  (min_le_right _ _).trans (Nat.sub_le _ _)

theorem tensorSecondSteps_le (c : StringSystem A) (d : StringSystem B) (x : A) (y : B) (k : ℕ)
    (hk : k ≤ (c.tensor d).phi (x, y)) :
    tensorSecondSteps c d x y k ≤ d.phi y := by
  change k ≤ d.phi y + (c.phi x - d.epsilon y) at hk
  unfold tensorSecondSteps tensorFirstSteps
  omega

/-- The exact literal tensor lowering iterate, with all component bounds
derived from the actual tensor string length. -/
theorem tensor_lowerAt_split (c : StringSystem A) (d : StringSystem B)
    (x : A) (y : B) (k : ℕ) (hk : k ≤ (c.tensor d).phi (x, y)) :
    (c.tensor d).lowerAt k (x, y) hk =
      (c.lowerAt (tensorFirstSteps c d x y k) x (tensorFirstSteps_le c d x y k),
        d.lowerAt (tensorSecondSteps c d x y k) y (tensorSecondSteps_le c d x y k hk)) := by
  induction k with
  | zero => simp [tensorFirstSteps, tensorSecondSteps, lowerAt_zero]
  | succ k ih =>
      have hk0 : k ≤ (c.tensor d).phi (x, y) := by omega
      have hstep := (c.tensor d).lowerAt_succ_step (x, y) k hk0 hk
      rw [ih hk0] at hstep
      by_cases hfirst : k < c.phi x - d.epsilon y
      · have hfirst0 : tensorFirstSteps c d x y k = k := by
          simp only [tensorFirstSteps, min_eq_left hfirst.le]
        have hfirst1 : tensorFirstSteps c d x y (k + 1) = k + 1 := by
          exact min_eq_left hfirst
        have hsecond0 : tensorSecondSteps c d x y k = 0 := by
          simp only [tensorSecondSteps, hfirst0, Nat.sub_self]
        have hsecond1 : tensorSecondSteps c d x y (k + 1) = 0 := by
          simp only [tensorSecondSteps, hfirst1, Nat.sub_self]
        have hkc : k ≤ c.phi x := by omega
        have hksc : k + 1 ≤ c.phi x := by omega
        have hstats := c.lowerAt_stats k x hkc
        have hcond : d.epsilon y < c.phi (c.lowerAt k x hkc) := by omega
        have hcstep := c.lowerAt_succ_step x k hkc hksc
        have hs : (c.tensor d).lowerAt (k + 1) (x, y) hk =
            (c.lowerAt (k + 1) x hksc, y) := by
          simpa only [hfirst0, hsecond0, lowerAt_zero, tensor, if_pos hcond,
            hcstep, Option.map_some, Option.some.injEq, eq_comm] using hstep
        simpa only [hfirst1, hsecond1, lowerAt_zero] using hs
      · have hfirst0 : tensorFirstSteps c d x y k = c.phi x - d.epsilon y := by
          exact min_eq_right (by omega)
        have hfirst1 : tensorFirstSteps c d x y (k + 1) = c.phi x - d.epsilon y := by
          exact min_eq_right (by omega)
        have hsecond1 : tensorSecondSteps c d x y (k + 1) =
            tensorSecondSteps c d x y k + 1 := by
          simp only [tensorSecondSteps, hfirst0, hfirst1]
          omega
        have hkc := tensorFirstSteps_le c d x y k
        have hkd := tensorSecondSteps_le c d x y k hk0
        have hksd : tensorSecondSteps c d x y k + 1 ≤ d.phi y := by
          have hh := tensorSecondSteps_le c d x y (k + 1) hk
          rwa [hsecond1] at hh
        have hstatsc := c.lowerAt_stats (tensorFirstSteps c d x y k) x hkc
        have hstatsd := d.lowerAt_stats (tensorSecondSteps c d x y k) y hkd
        have hcond : ¬ d.epsilon (d.lowerAt (tensorSecondSteps c d x y k) y hkd) <
            c.phi (c.lowerAt (tensorFirstSteps c d x y k) x hkc) := by
          omega
        have hdstep := d.lowerAt_succ_step y (tensorSecondSteps c d x y k) hkd hksd
        have hs : (c.tensor d).lowerAt (k + 1) (x, y) hk =
            (c.lowerAt (tensorFirstSteps c d x y k) x hkc,
              d.lowerAt (tensorSecondSteps c d x y k + 1) y hksd) := by
          simpa only [tensor, if_neg hcond, hdstep, Option.map_some,
            Option.some.injEq, eq_comm] using hstep
        simpa only [hfirst0, hfirst1, hsecond1] using hs

theorem tensor_weight_balance (c : StringSystem A) (d : StringSystem B) (x : A) (y : B) :
    ((c.tensor d).phi (x, y) : ℤ) - (c.tensor d).epsilon (x, y) =
      (c.phi x : ℤ) + d.phi y - c.epsilon x - d.epsilon y := by
  simp only [tensor]
  omega

theorem tensor_reflection_direction_swap (c : StringSystem A) (d : StringSystem B)
    (x : A) (y : B) :
    (c.tensor d).epsilon (x, y) ≤ (c.tensor d).phi (x, y) ↔
      (d.tensor c).epsilon (y, x) ≤ (d.tensor c).phi (y, x) := by
  have h := tensor_weight_balance c d x y
  have h' := tensor_weight_balance d c y x
  omega

theorem tensor_reflection_lower_count_swap (c : StringSystem A) (d : StringSystem B)
    (x : A) (y : B) :
    (c.tensor d).phi (x, y) - (c.tensor d).epsilon (x, y) =
      (d.tensor c).phi (y, x) - (d.tensor c).epsilon (y, x) := by
  have h := tensor_weight_balance c d x y
  have h' := tensor_weight_balance d c y x
  omega

/-- At the full reflection length, the first factor's step count is the
second factor's count after swapping the factors. -/
theorem tensor_reflection_steps_swap (c : StringSystem A) (d : StringSystem B)
    (x : A) (y : B)
    (h : (c.tensor d).epsilon (x, y) ≤ (c.tensor d).phi (x, y)) :
    tensorFirstSteps c d x y ((c.tensor d).phi (x, y) - (c.tensor d).epsilon (x, y)) =
      tensorSecondSteps d c y x ((d.tensor c).phi (y, x) - (d.tensor c).epsilon (y, x)) := by
  have hweight := tensor_weight_balance c d x y
  have hsame := tensor_reflection_lower_count_swap c d x y
  simp only [tensorSecondSteps, tensorFirstSteps]
  rw [← hsame]
  omega

theorem tensor_reflection_swap_of_lower_direction (c : StringSystem A) (d : StringSystem B)
    (x : A) (y : B)
    (h : (c.tensor d).epsilon (x, y) ≤ (c.tensor d).phi (x, y)) :
    (d.tensor c).reflection (y, x) = Prod.swap ((c.tensor d).reflection (x, y)) := by
  have h' := (tensor_reflection_direction_swap c d x y).mp h
  have hs := tensor_reflection_steps_swap c d x y h
  have hs' := tensor_reflection_steps_swap d c y x h'
  rw [reflection, dif_pos h', reflection, dif_pos h]
  rw [tensor_lowerAt_split, tensor_lowerAt_split]
  simp only [Prod.swap_prod_mk]
  congr 1
  · simp only [hs']
  · simp only [hs]

theorem ext_functions {c d : StringSystem A}
    (hr : c.raise = d.raise) (hl : c.lower = d.lower)
    (he : c.epsilon = d.epsilon) (hp : c.phi = d.phi) : c = d := by
  cases c
  cases d
  cases hr
  cases hl
  cases he
  cases hp
  rfl

theorem reverse_tensor_swap (c : StringSystem A) (d : StringSystem B) :
    (c.tensor d).reverse =
      (d.reverse.tensor c.reverse).transport (Equiv.prodComm B A) := by
  apply ext_functions
  · funext x
    rcases x with ⟨x, y⟩
    by_cases h : d.epsilon y < c.phi x
    · simp [reverse, tensor, transport, h, show ¬ c.phi x ≤ d.epsilon y by omega,
        Option.map_map, Function.comp_def]
    · simp [reverse, tensor, transport, h, show c.phi x ≤ d.epsilon y by omega,
        Option.map_map, Function.comp_def]
  · funext x
    rcases x with ⟨x, y⟩
    by_cases h : d.epsilon y ≤ c.phi x
    · simp [reverse, tensor, transport, h, show ¬ c.phi x < d.epsilon y by omega,
        Option.map_map, Function.comp_def]
    · simp [reverse, tensor, transport, h, show c.phi x < d.epsilon y by omega,
        Option.map_map, Function.comp_def]
  · rfl
  · rfl

theorem transport_lowerIterate (c : StringSystem A) (e : A ≃ B) (k : ℕ) (y : B) :
    (c.transport e).lowerIterate k y = (c.lowerIterate k (e.symm y)).map e := by
  induction k generalizing y with
  | zero => simp [lowerIterate, partialIterate]
  | succ k ih =>
      change ((c.lower (e.symm y)).map e).bind ((c.transport e).lowerIterate k) =
        ((c.lower (e.symm y)).bind (c.lowerIterate k)).map e
      cases h : c.lower (e.symm y) with
      | none => simp [h]
      | some x => simp [h, ih]

theorem reverse_transport (c : StringSystem A) (e : A ≃ B) :
    (c.transport e).reverse = c.reverse.transport e := rfl

theorem transport_reflection (c : StringSystem A) (e : A ≃ B) (y : B) :
    (c.transport e).reflection y = e (c.reflection (e.symm y)) := by
  unfold reflection
  change (if h : c.epsilon (e.symm y) ≤ c.phi (e.symm y) then _ else _) = _
  split_ifs with h
  · have ht := transport_lowerIterate c e
      (c.phi (e.symm y) - c.epsilon (e.symm y)) y
    rw [c.lowerAt_spec _ (e.symm y) (Nat.sub_le _ _), Option.map_some] at ht
    have hs := (c.transport e).lowerAt_spec
      (c.phi (e.symm y) - c.epsilon (e.symm y)) y (Nat.sub_le _ _)
    rw [ht] at hs
    exact (Option.some.inj hs).symm
  · have ht := transport_lowerIterate c.reverse e
      (c.epsilon (e.symm y) - c.phi (e.symm y)) y
    rw [c.reverse.lowerAt_spec
      (c.epsilon (e.symm y) - c.phi (e.symm y)) (e.symm y) (Nat.sub_le _ _),
      Option.map_some] at ht
    have hs := (c.transport e).reverse.lowerAt_spec
      (c.epsilon (e.symm y) - c.phi (e.symm y)) y (Nat.sub_le _ _)
    have hsame := congrArg
      (fun d : StringSystem B =>
        d.lowerIterate (c.epsilon (e.symm y) - c.phi (e.symm y)) y)
      (reverse_transport c e)
    exact Option.some.inj (hs.symm.trans (hsame.trans ht))

theorem reflection_reverse (c : StringSystem A) (x : A) :
    c.reverse.reflection x = c.reflection x := by
  rcases lt_trichotomy (c.epsilon x) (c.phi x) with h | h | h
  · have hr : ¬ c.reverse.epsilon x ≤ c.reverse.phi x := by
      change ¬ c.phi x ≤ c.epsilon x
      omega
    rw [reflection, dif_neg hr, reflection, dif_pos h.le]
    rfl
  · rw [c.reflection_eq_self_of_middle h,
      c.reverse.reflection_eq_self_of_middle (show c.reverse.epsilon x = c.reverse.phi x from h.symm)]
  · have hr : c.reverse.epsilon x ≤ c.reverse.phi x := h.le
    rw [reflection, dif_pos hr, reflection, dif_neg (not_le.mpr h)]
    rfl

theorem tensor_reflection_reverse_formula (c : StringSystem A) (d : StringSystem B)
    (x : A) (y : B) :
    (c.tensor d).reflection (x, y) =
      Prod.swap ((d.reverse.tensor c.reverse).reflection (y, x)) := by
  rw [← reflection_reverse, reverse_tensor_swap, transport_reflection]
  rfl

/-- Rank-one string reflection commutes with exchanging two complete tensor
factors.  This is a statement about reflection, not a false assertion that
raising and lowering themselves commute with that exchange. -/
theorem tensor_reflection_swap (c : StringSystem A) (d : StringSystem B)
    (x : A) (y : B) :
    (d.tensor c).reflection (y, x) = Prod.swap ((c.tensor d).reflection (x, y)) := by
  by_cases h : (c.tensor d).epsilon (x, y) ≤ (c.tensor d).phi (x, y)
  · exact tensor_reflection_swap_of_lower_direction c d x y h
  · have hrev : (c.reverse.tensor d.reverse).epsilon (x, y) ≤
        (c.reverse.tensor d.reverse).phi (x, y) := by
      have h₁ := tensor_weight_balance c d x y
      have h₂ := tensor_weight_balance c.reverse d.reverse x y
      simp only [tensor, reverse_epsilon, reverse_phi] at h h₁ h₂ ⊢
      omega
    have hh := tensor_reflection_swap_of_lower_direction c.reverse d.reverse x y hrev
    rw [tensor_reflection_reverse_formula d c y x,
      tensor_reflection_reverse_formula c d x y, Prod.swap_swap]
    exact hh.symm

theorem lowerIterate_map (c : StringSystem A) (d : StringSystem B) (f : A → B)
    (hl : ∀ x, d.lower (f x) = (c.lower x).map f) (k : ℕ) (x : A) :
    d.lowerIterate k (f x) = (c.lowerIterate k x).map f := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      change (d.lower (f x)).bind (d.lowerIterate k) =
        ((c.lower x).bind (c.lowerIterate k)).map f
      rw [hl]
      cases h : c.lower x <;> simp [h, ih]

theorem reflection_map (c : StringSystem A) (d : StringSystem B) (f : A → B)
    (he : ∀ x, d.epsilon (f x) = c.epsilon x)
    (hp : ∀ x, d.phi (f x) = c.phi x)
    (hl : ∀ x, d.lower (f x) = (c.lower x).map f)
    (hr : ∀ x, d.raise (f x) = (c.raise x).map f) (x : A) :
    d.reflection (f x) = f (c.reflection x) := by
  by_cases h : c.epsilon x ≤ c.phi x
  · have hd : d.epsilon (f x) ≤ d.phi (f x) := by simpa only [he, hp] using h
    rw [reflection, dif_pos hd, reflection, dif_pos h]
    have ht := lowerIterate_map c d f hl (c.phi x - c.epsilon x) x
    have hs : d.lowerIterate (c.phi x - c.epsilon x) (f x) =
        some (d.lowerAt (d.phi (f x) - d.epsilon (f x)) (f x) (Nat.sub_le _ _)) := by
      rw [← hp x, ← he x]
      exact d.lowerAt_spec _ (f x) (Nat.sub_le _ _)
    rw [hs, c.lowerAt_spec _ x (Nat.sub_le _ _), Option.map_some] at ht
    exact Option.some.inj ht
  · have hd : ¬ d.epsilon (f x) ≤ d.phi (f x) := by simpa only [he, hp] using h
    rw [reflection, dif_neg hd, reflection, dif_neg h]
    have ht := lowerIterate_map c.reverse d.reverse f hr (c.epsilon x - c.phi x) x
    have hs : d.reverse.lowerIterate (c.epsilon x - c.phi x) (f x) =
        some (d.reverse.lowerAt (d.epsilon (f x) - d.phi (f x)) (f x)
          (Nat.sub_le (d.epsilon (f x)) (d.phi (f x)))) := by
      rw [← he x, ← hp x]
      exact d.reverse.lowerAt_spec (d.epsilon (f x) - d.phi (f x)) (f x) (Nat.sub_le _ _)
    rw [hs, c.reverse.lowerAt_spec (c.epsilon x - c.phi x) x (Nat.sub_le _ _),
      Option.map_some] at ht
    exact Option.some.inj ht

end HigherSpecht.Lascoux.StringSystem
end
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/LascouxNeutralFilter.lean -/



/-!
# Deleting neutral high letters commutes with the actual crystal operators

The filter keeps exactly the letters below a fixed bound.  For a signature
operator whose two letters are below that bound, the discarded letters
are neutral factors.  The proof follows the literal cons recursion and
then the actual string-reflection construction.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def alphabetFilter (K : ℕ) (w : List ℕ) : List ℕ := w.filter (fun a => decide (a < K))

theorem alphabetFilter_cons (K a : ℕ) (w : List ℕ) :
    alphabetFilter K (a :: w) =
      if a < K then a :: alphabetFilter K w else alphabetFilter K w := by
  by_cases ha : a < K <;> simp [alphabetFilter, ha]

theorem listString_epsilon_filter (K r : ℕ) (hr : r + 1 < K) (w : List ℕ) :
    (listString r).epsilon (alphabetFilter K w) = (listString r).epsilon w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [alphabetFilter_cons]
      by_cases ha : a < K
      · rw [if_pos ha, listString_epsilon_cons, listString_epsilon_cons, ih]
        congr 1
        have hphi : (listString r).phi (alphabetFilter K w) = (listString r).phi w := by
          have hb := listString_balance r (alphabetFilter K w)
          have hb' := listString_balance r w
          have hc0 : (alphabetFilter K w).count r = w.count r := by
            simp [alphabetFilter, show r < K by omega]
          have hc1 : (alphabetFilter K w).count (r + 1) = w.count (r + 1) := by
            simp [alphabetFilter, hr]
          rw [hc0, hc1, ih] at hb
          omega
        rw [hphi]
      · have har : a ≠ r := by omega
        have har' : a ≠ r + 1 := by omega
        rw [if_neg ha, listString_neutral_epsilon r a w har har', ih]

theorem listString_phi_filter (K r : ℕ) (hr : r + 1 < K) (w : List ℕ) :
    (listString r).phi (alphabetFilter K w) = (listString r).phi w := by
  have he := listString_epsilon_filter K r hr w
  have hb := listString_balance r (alphabetFilter K w)
  have hb' := listString_balance r w
  have hc0 : (alphabetFilter K w).count r = w.count r := by
    simp [alphabetFilter, show r < K by omega]
  have hc1 : (alphabetFilter K w).count (r + 1) = w.count (r + 1) := by
    simp [alphabetFilter, hr]
  rw [hc0, hc1, he] at hb
  omega

theorem listString_lower_filter (K r : ℕ) (hr : r + 1 < K) (w : List ℕ) :
    (listString r).lower (alphabetFilter K w) =
      ((listString r).lower w).map (alphabetFilter K) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [alphabetFilter_cons]
      by_cases ha : a < K
      · rw [if_pos ha, listString_lower_cons, listString_lower_cons,
          listString_phi_filter K r hr w]
        split_ifs with hbranch
        · rw [ih]
          simp only [Option.map_map, Function.comp_def, alphabetFilter_cons, if_pos ha]
        · by_cases har : a = r
          · subst a
            simp only [letterString_lower, if_pos rfl, ite_true, Option.map_some,
              alphabetFilter_cons, if_pos hr]
          · simp only [letterString_lower, if_neg har, Option.map_none]
      · have har : a ≠ r := by omega
        have har' : a ≠ r + 1 := by omega
        rw [if_neg ha, listString_neutral_lower r a w har har', ih]
        simp only [Option.map_map, Function.comp_def, alphabetFilter_cons, if_neg ha]

theorem listString_raise_filter (K r : ℕ) (hr : r + 1 < K) (w : List ℕ) :
    (listString r).raise (alphabetFilter K w) =
      ((listString r).raise w).map (alphabetFilter K) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [alphabetFilter_cons]
      by_cases ha : a < K
      · rw [if_pos ha, listString_raise_cons, listString_raise_cons,
          listString_phi_filter K r hr w]
        split_ifs with hbranch
        · rw [ih]
          simp only [Option.map_map, Function.comp_def, alphabetFilter_cons, if_pos ha]
        · by_cases har : a = r + 1
          · subst a
            simp only [letterString_raise, if_pos rfl, ite_true, Option.map_some,
              alphabetFilter_cons, if_pos (show r < K by omega)]
          · simp only [letterString_raise, if_neg har, Option.map_none]
      · have har : a ≠ r := by omega
        have har' : a ≠ r + 1 := by omega
        rw [if_neg ha, listString_neutral_raise r a w har har', ih]
        simp only [Option.map_map, Function.comp_def, alphabetFilter_cons, if_neg ha]

theorem listString_reflection_filter (K r : ℕ) (hr : r + 1 < K) (w : List ℕ) :
    (listString r).reflection (alphabetFilter K w) =
      alphabetFilter K ((listString r).reflection w) := by
  exact StringSystem.reflection_map (listString r) (listString r) (alphabetFilter K)
    (listString_epsilon_filter K r hr) (listString_phi_filter K r hr)
    (listString_lower_filter K r hr) (listString_raise_filter K r hr) w

def PreservesWordFilter (K : ℕ) {N L : ℕ}
    (e : (Fin N → ℕ) ≃ (Fin N → ℕ)) (f : (Fin L → ℕ) ≃ (Fin L → ℕ)) : Prop :=
  ∀ u v, alphabetFilter K (List.ofFn (e u)) = List.ofFn (f v) ↔
    alphabetFilter K (List.ofFn u) = List.ofFn v

theorem PreservesWordFilter.refl (K N L : ℕ) :
    PreservesWordFilter K (Equiv.refl (Fin N → ℕ)) (Equiv.refl (Fin L → ℕ)) :=
  fun _ _ => Iff.rfl

theorem PreservesWordFilter.trans {K N L : ℕ}
    {e₁ e₂ : (Fin N → ℕ) ≃ (Fin N → ℕ)}
    {f₁ f₂ : (Fin L → ℕ) ≃ (Fin L → ℕ)}
    (h₁ : PreservesWordFilter K e₁ f₁) (h₂ : PreservesWordFilter K e₂ f₂) :
    PreservesWordFilter K (e₁.trans e₂) (f₁.trans f₂) := by
  intro u v
  exact (h₂ (e₁ u) (f₁ v)).trans (h₁ u v)

theorem PreservesWordFilter.symm {K N L : ℕ}
    {e : (Fin N → ℕ) ≃ (Fin N → ℕ)} {f : (Fin L → ℕ) ≃ (Fin L → ℕ)}
    (h : PreservesWordFilter K e f) : PreservesWordFilter K e.symm f.symm := by
  intro u v
  simpa only [Equiv.apply_symm_apply] using (h (e.symm u) (f.symm v)).symm

theorem wordReflection_preserves_filter (K r N L : ℕ) (hr : r + 1 < K) :
    PreservesWordFilter K (wordReflection r N) (wordReflection r L) := by
  have hf {u : Fin N → ℕ} {v : Fin L → ℕ}
      (h : alphabetFilter K (List.ofFn u) = List.ofFn v) :
      alphabetFilter K (List.ofFn (wordReflection r N u)) =
        List.ofFn (wordReflection r L v) := by
    rw [← listString_reflection_ofFn, ← listString_reflection_filter K r hr,
      h, listString_reflection_ofFn]
  intro u v
  constructor
  · intro h
    have hh := hf h
    rw [wordReflection_involutive r N u, wordReflection_involutive r L v] at hh
    exact hh
  · exact hf

theorem wordSwapZero_preserves_filter (K j N L : ℕ) (hj : j < K) :
    PreservesWordFilter K (wordSwapZero N j) (wordSwapZero L j) := by
  revert hj
  induction j using Nat.twoStepInduction with
  | zero => intro hj; exact PreservesWordFilter.refl K N L
  | one => intro hj; exact wordReflection_preserves_filter K 0 N L hj
  | more j ih ih' =>
      intro hj
      exact (wordReflection_preserves_filter K (j + 1) N L hj).trans
        ((ih' (by omega)).trans (wordReflection_preserves_filter K (j + 1) N L hj))

theorem wordContentSwap_preserves_filter (K i j N L : ℕ) (hi : i < K) (hj : j < K) :
    PreservesWordFilter K (wordContentSwap N i j) (wordContentSwap L i j) := by
  unfold wordContentSwap
  split_ifs
  · exact PreservesWordFilter.refl K N L
  · exact wordSwapZero_preserves_filter K j N L hj
  · exact wordSwapZero_preserves_filter K i N L hi
  · exact (wordSwapZero_preserves_filter K i N L hi).trans
      ((wordSwapZero_preserves_filter K j N L hj).trans
        (wordSwapZero_preserves_filter K i N L hi))

theorem wordBringPair_preserves_filter (K i j N L : ℕ) (hi : i < K) (hj : j < K)
    (hij : i ≠ j) :
    PreservesWordFilter K (wordBringPair N i j) (wordBringPair L i j) := by
  have hK : 1 < K := by omega
  have hswap : Equiv.swap 0 i j < K := by
    by_cases h0 : j = 0
    · subst j
      simpa using hi
    · by_cases hji : j = i
      · exact (hij hji.symm).elim
      · simpa only [Equiv.swap_apply_of_ne_of_ne h0 hji] using hj
  exact (wordContentSwap_preserves_filter K 0 i N L (by omega) hi).trans
    (wordContentSwap_preserves_filter K 1 (Equiv.swap 0 i j) N L hK hswap)

end HigherSpecht.Lascoux
end
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/LascouxSaturatedReconstruction.lean -/



/-!
# Reconstructing the saturated base from its genuine recursive tableau

Deleting letters above a threshold is literal tableau restriction and
literal word filtering.  Conversely a zero first row can be attached to
an arbitrary semistandard tableau on the actual first-row-tail shape.
These are geometric identities of the original tableaux; no image or
catabolizability condition enters their definitions.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

theorem alphabetRestrictionShape_rowLen (T : SemistandardYoungTableau mu)
    (M r : ℕ) : (alphabetRestrictionShape T M).rowLen r = T.rowCountLt r M := by
  have h (j : ℕ) : j < (alphabetRestrictionShape T M).rowLen r ↔
      j < T.rowCountLt r M := by
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_alphabetRestrictionShape]
    constructor
    · rintro ⟨hj, hval⟩
      exact (T.lt_rowCountLt_iff (YoungDiagram.mem_iff_lt_rowLen.mp hj)).mpr hval
    · intro hj
      have hj' := hj.trans_le (T.rowCountLt_le_rowLen r M)
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hj', (T.lt_rowCountLt_iff hj').mp hj⟩
  have h₁ := h ((alphabetRestrictionShape T M).rowLen r)
  have h₂ := h (T.rowCountLt r M)
  omega

theorem alphabetRestrictionShape_height_le (T : SemistandardYoungTableau mu) (M : ℕ) :
    (alphabetRestrictionShape T M).colLen 0 ≤ mu.colLen 0 := by
  by_contra h
  have hm : (mu.colLen 0, 0) ∈ alphabetRestrictionShape T M :=
    YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_ge h)
  have hp := YoungDiagram.mem_iff_lt_colLen.mp
    ((mem_alphabetRestrictionShape T M _ _).mp hm).1
  exact (Nat.lt_irrefl _) hp

theorem tableauRowWord_nil_of_height_le (T : SemistandardYoungTableau mu)
    {r : ℕ} (hr : mu.colLen 0 ≤ r) : tableauRowWord T r = [] := by
  apply List.length_eq_zero_iff.mp
  rw [tableauRowWord_length]
  exact YoungDiagram.rowLen_eq_zero_of_colLen_le hr

theorem tableauWord_withHeight (T : SemistandardYoungTableau mu)
    (H : ℕ) (hH : mu.colLen 0 ≤ H) :
    (descendingRows H).flatMap (tableauRowWord T) = tableauWord T := by
  induction H with
  | zero =>
      have hh : mu.colLen 0 = 0 := by omega
      simp only [tableauWord, hh]
  | succ H ih =>
      by_cases hh : mu.colLen 0 ≤ H
      · simp only [descendingRows, List.flatMap_cons,
          tableauRowWord_nil_of_height_le T hh, List.nil_append]
        exact ih hh
      · have heq : mu.colLen 0 = H + 1 := by omega
        simp only [tableauWord, heq]

theorem tableauRowWord_alphabetRestriction (T : SemistandardYoungTableau mu)
    (M r : ℕ) :
    tableauRowWord (alphabetRestriction T M) r =
      alphabetFilter M (tableauRowWord T r) := by
  have hcut := T.rowCountLt_le_rowLen r M
  have hrow : tableauRowWord (alphabetRestriction T M) r =
      tableauRowSegment T r 0 (T.rowCountLt r M) := by
    unfold tableauRowWord
    rw [alphabetRestrictionShape_rowLen]
    unfold tableauRowSegment
    apply List.map_congr_left
    intro j hj
    obtain ⟨k, hk, hkj⟩ := List.mem_range'.mp hj
    have hjcut : j < T.rowCountLt r M := by omega
    have hjlen := hjcut.trans_le hcut
    have hmem : (r, j) ∈ alphabetRestrictionShape T M :=
      (mem_alphabetRestrictionShape T M r j).mpr
        ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hjlen, (T.lt_rowCountLt_iff hjlen).mp hjcut⟩
    simp only [alphabetRestriction_apply, if_pos hmem]
  rw [hrow]
  have hsplit := tableauRowSegment_append T r 0 (T.rowCountLt r M) (mu.rowLen r)
    (Nat.zero_le _) hcut
  change _ = alphabetFilter M (tableauRowSegment T r 0 (mu.rowLen r))
  rw [← hsplit]
  unfold alphabetFilter
  rw [List.filter_append]
  have hbefore :
      (tableauRowSegment T r 0 (T.rowCountLt r M)).filter (fun a => a < M) =
        tableauRowSegment T r 0 (T.rowCountLt r M) := by
    apply List.filter_eq_self.mpr
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    obtain ⟨k, hk, hkj⟩ := List.mem_range'.mp hj
    have hjcut : j < T.rowCountLt r M := by omega
    simpa only [decide_eq_true_eq] using
      (T.lt_rowCountLt_iff (hjcut.trans_le hcut)).mp hjcut
  have hafter :
      (tableauRowSegment T r (T.rowCountLt r M) (mu.rowLen r)).filter
        (fun a => a < M) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    obtain ⟨k, hk, hkj⟩ := List.mem_range'.mp hj
    have hjlen : j < mu.rowLen r := by omega
    have hjge : T.rowCountLt r M ≤ j := by omega
    have hiff := T.lt_rowCountLt_iff (x := M) hjlen
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    omega
  rw [hbefore, hafter, List.append_nil]

theorem tableauWord_alphabetRestriction (T : SemistandardYoungTableau mu) (M : ℕ) :
    tableauWord (alphabetRestriction T M) = alphabetFilter M (tableauWord T) := by
  rw [← tableauWord_withHeight (alphabetRestriction T M) (mu.colLen 0)
    (alphabetRestrictionShape_height_le T M)]
  unfold tableauWord alphabetFilter
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro r hr
  exact tableauRowWord_alphabetRestriction T M r

def prependZeroRow (U : SemistandardYoungTableau (firstRowTail mu)) :
    SemistandardYoungTableau mu where
  entry i j := if (i, j) ∈ mu then if i = 0 then 0 else U (i - 1) j + 1 else 0
  row_weak' {i j k} hj hk := by
    have hij := mu.up_left_mem le_rfl hj.le hk
    simp only [if_pos hij, if_pos hk]
    by_cases hi : i = 0
    · simp only [if_pos hi]
      exact le_rfl
    · simp only [if_neg hi]
      apply Nat.add_le_add_right
      apply U.row_weak hj
      exact (mem_firstRowTail mu _ _).mpr (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hk)
  col_strict' {i k j} hik hk := by
    have hij := mu.up_left_mem hik.le le_rfl hk
    have hk0 : k ≠ 0 := by omega
    simp only [if_pos hij, if_pos hk, if_neg hk0]
    by_cases hi : i = 0
    · simp only [if_pos hi]
      omega
    · simp only [if_neg hi]
      apply Nat.add_lt_add_right
      apply U.col_strict (by omega : i - 1 < k - 1)
      exact (mem_firstRowTail mu _ _).mpr (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hk)
  zeros' {i j} hij := by simp only [if_neg hij]

@[simp] theorem prependZeroRow_zero (U : SemistandardYoungTableau (firstRowTail mu))
    (j : ℕ) : prependZeroRow U 0 j = 0 := by
  change (if (0, j) ∈ mu then 0 else 0) = 0
  split_ifs <;> rfl

theorem prependZeroRow_succ (U : SemistandardYoungTableau (firstRowTail mu))
    (i j : ℕ) (hij : (i, j) ∈ firstRowTail mu) :
    prependZeroRow U (i + 1) j = U i j + 1 := by
  change (if (i + 1, j) ∈ mu then
    if i + 1 = 0 then 0 else U (i + 1 - 1) j + 1 else 0) = U i j + 1
  simp only [if_pos ((mem_firstRowTail mu i j).mp hij),
    Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]

@[simp] theorem firstRowTailPred_prependZeroRow
    (U : SemistandardYoungTableau (firstRowTail mu)) :
    firstRowTailPred (prependZeroRow U) = U := by
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hij : (i, j) ∈ firstRowTail mu
  · rw [firstRowTailPred_apply, prependZeroRow_succ U i j hij]
    omega
  · rw [(firstRowTailPred (prependZeroRow U)).zeros hij, U.zeros hij]

theorem prependZeroRow_saturated (U : SemistandardYoungTableau (firstRowTail mu)) :
    (contentCells (prependZeroRow U) 0).card = mu.rowLen 0 := by
  have hcells : contentCells (prependZeroRow U) 0 =
      (Finset.range (mu.rowLen 0)).image (fun j => (0, j)) := by
    ext c
    rcases c with ⟨i, j⟩
    simp only [contentCells, Finset.mem_filter, YoungDiagram.mem_cells,
      Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨hij, hzero⟩
      have hi := zero_cell_row hij hzero
      subst i
      exact ⟨j, YoungDiagram.mem_iff_lt_rowLen.mp hij, rfl, rfl⟩
    · rintro ⟨k, hk, hi, hkj⟩
      subst i
      subst j
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hk, prependZeroRow_zero U k⟩
  rw [hcells, Finset.card_image_of_injective _ (by
    intro a b hab
    exact congrArg Prod.snd hab), Finset.card_range]

theorem prependZeroRow_bound (U : SemistandardYoungTableau (firstRowTail mu))
    (M : ℕ) (hU : ∀ i j, (i, j) ∈ firstRowTail mu → U i j < M) :
    ∀ i j, (i, j) ∈ mu → prependZeroRow U i j ≤ M := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    rw [prependZeroRow_zero]
    exact Nat.zero_le _
  · have his : i - 1 + 1 = i := by omega
    have ht : (i - 1, j) ∈ firstRowTail mu :=
      (mem_firstRowTail mu _ _).mpr (by simpa only [his] using hij)
    have hb := hU (i - 1) j ht
    have he := prependZeroRow_succ U (i - 1) j ht
    rw [his] at he
    omega

theorem descendingRows_succ_map (H : ℕ) :
    descendingRows (H + 1) = (descendingRows H).map Nat.succ ++ [0] := by
  induction H with
  | zero => rfl
  | succ H ih =>
      simp only [descendingRows, List.map_cons, List.cons_append]
      exact congrArg (List.cons (H + 1)) ih

theorem tableauRowWord_prependZeroRow_succ
    (Q : SemistandardYoungTableau (firstRowTail mu)) (r : ℕ) :
    tableauRowWord (prependZeroRow Q) (r + 1) =
      (tableauRowWord Q r).map Nat.succ := by
  apply List.ext_getElem
  · rw [List.length_map, tableauRowWord_length, tableauRowWord_length,
      firstRowTail_rowLen]
  · intro j hj hj'
    rw [tableauRowWord_getElem, List.getElem_map, tableauRowWord_getElem]
    apply prependZeroRow_succ
    exact YoungDiagram.mem_iff_lt_rowLen.mpr (by
      simpa only [List.length_map, tableauRowWord_length] using hj')

theorem tableauRowWord_prependZeroRow_zero
    (Q : SemistandardYoungTableau (firstRowTail mu)) :
    tableauRowWord (prependZeroRow Q) 0 = List.replicate (mu.rowLen 0) 0 := by
  apply List.ext_getElem
  · rw [tableauRowWord_length, List.length_replicate]
  · intro j hj hj'
    rw [tableauRowWord_getElem, prependZeroRow_zero, List.getElem_replicate]

theorem tableauWord_prependZeroRow
    (Q : SemistandardYoungTableau (firstRowTail mu)) :
    tableauWord (prependZeroRow Q) =
      (tableauWord Q).map Nat.succ ++ List.replicate (mu.rowLen 0) 0 := by
  by_cases hh : mu.colLen 0 = 0
  · have hw : mu.rowLen 0 = 0 := YoungDiagram.rowLen_eq_zero_of_colLen_le (by omega)
    simp only [tableauWord, firstRowTail_colLen, hh, Nat.zero_sub,
      descendingRows, List.flatMap_nil, List.map_nil, hw, List.replicate_zero,
      List.append_nil]
  · have hH : (mu.colLen 0 - 1) + 1 = mu.colLen 0 := by omega
    have hrows : descendingRows (mu.colLen 0) =
        (descendingRows (mu.colLen 0 - 1)).map Nat.succ ++ [0] := by
      rw [← hH]
      exact descendingRows_succ_map _
    simp only [tableauWord, hrows, List.flatMap_append, List.flatMap_map,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      tableauRowWord_prependZeroRow_zero, firstRowTail_colLen]
    congr 1
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro r hr
    exact tableauRowWord_prependZeroRow_succ Q r

theorem tableauWord_eq_of_heq {nu : YoungDiagram}
    {T : SemistandardYoungTableau mu} {U : SemistandardYoungTableau nu}
    (hshape : mu = nu) (h : HEq T U) : tableauWord T = tableauWord U := by
  subst nu
  exact congrArg tableauWord (eq_of_heq h)

theorem alphabetFilter_saturatedSweep (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (M : ℕ)
    (hbound : ∀ i j, (i, j) ∈ mu → T i j ≤ M) :
    alphabetFilter M (tableauWord (saturatedSweep T M)) =
      tableauWord (firstRowTailPred T) := by
  rw [← tableauWord_alphabetRestriction]
  exact tableauWord_eq_of_heq (saturatedSweep_restriction T hs M hbound).1
    (saturatedSweep_restriction T hs M hbound).2

/-- A maximal-letter completion of a fixed-shape tableau is determined
by its literal subalphabet word.  The equality is about all cells. -/
theorem tableau_eq_of_alphabetFilter (T U : SemistandardYoungTableau mu) (M : ℕ)
    (hT : ∀ i j, (i, j) ∈ mu → T i j ≤ M)
    (hU : ∀ i j, (i, j) ∈ mu → U i j ≤ M)
    (hword : alphabetFilter M (tableauWord T) = alphabetFilter M (tableauWord U)) :
    T = U := by
  have hk : KnuthEquivalent (tableauWord (alphabetRestriction T M))
      (tableauWord (alphabetRestriction U M)) := by
    rw [tableauWord_alphabetRestriction, tableauWord_alphabetRestriction, hword]
    exact .refl _
  have hshape := shape_eq_of_knuth_tableauWord _ _ hk
  have hentries := entries_eq_of_knuth_tableauWord _ _ hk
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hc : (i, j) ∈ mu
  · by_cases ht : T i j < M
    · have hct : (i, j) ∈ alphabetRestrictionShape T M :=
        (mem_alphabetRestrictionShape T M i j).mpr ⟨hc, ht⟩
      have hcu : (i, j) ∈ alphabetRestrictionShape U M := by
        simpa only [hshape] using hct
      have he := hentries i j
      simpa only [alphabetRestriction_apply, if_pos hct, if_pos hcu] using he
    · have hu : ¬ U i j < M := by
        intro hu
        have hcu : (i, j) ∈ alphabetRestrictionShape U M :=
          (mem_alphabetRestrictionShape U M i j).mpr ⟨hc, hu⟩
        have hct : (i, j) ∈ alphabetRestrictionShape T M := by
          simpa only [hshape] using hcu
        exact ht ((mem_alphabetRestrictionShape T M i j).mp hct).2
      have htb := hT i j hc
      have hub := hU i j hc
      omega
  · rw [T.zeros hc, U.zeros hc]

theorem saturatedSweep_bound (T : SemistandardYoungTableau mu)
    (hs : (contentCells T 0).card = mu.rowLen 0) (M : ℕ)
    (hbound : ∀ i j, (i, j) ∈ mu → T i j ≤ M) :
    ∀ i j, (i, j) ∈ mu → saturatedSweep T M i j ≤ M := by
  intro i j hij
  rw [saturatedSweep_entry T hs M hbound i j hij]
  split_ifs with hnext
  · exact (Nat.sub_le _ _).trans (hbound (i + 1) j hnext)
  · exact le_rfl

end HigherSpecht.Lascoux
end
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/Polynomials.lean -/



/-!
# The actual higher Specht polynomials and the elementary ideals

The coefficient ring is arbitrary.  In particular the column-after-row
symmetrizer is not divided by its hook product or by a factorial.  All quotient
definitions retain the manuscript's complete elementary generators.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset MvPolynomial TauCeti
open TauCeti.YoungTableau

namespace HigherSpecht

abbrev PolynomialRing (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin n) R

variable {R : Type*} [CommRing R]

/-- The elementary symmetric polynomial in precisely the variables in Y. -/
def elementaryOn {n : ℕ} (Y : Finset (Fin n)) (d : ℕ) : PolynomialRing n R :=
  ∑ A ∈ Y.powersetCard d, ∏ i ∈ A, X i

@[simp] theorem elementaryOn_zero {n : ℕ} (Y : Finset (Fin n)) :
    elementaryOn (R := R) Y 0 = 1 := by
  simp [elementaryOn]

theorem elementaryOn_eq_zero_of_card_lt {n : ℕ} {Y : Finset (Fin n)} {d : ℕ}
    (hd : Y.card < d) : elementaryOn (R := R) Y d = 0 := by
  simp [elementaryOn, Finset.powersetCard_eq_empty.mpr hd]

@[simp] theorem elementaryOn_univ {n : ℕ} (d : ℕ) :
    elementaryOn (R := R) (Finset.univ : Finset (Fin n)) d =
      MvPolynomial.esymm (Fin n) R d := rfl

theorem constantCoeff_elementaryOn {n : ℕ} (Y : Finset (Fin n)) {d : ℕ}
    (hd : 0 < d) : constantCoeff (elementaryOn (R := R) Y d) = 0 := by
  classical
  simp only [elementaryOn, map_sum, map_prod, constantCoeff_X]
  apply Finset.sum_eq_zero
  intro A hA
  have hcard : A.card = d := (Finset.mem_powersetCard.mp hA).2
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  exact Finset.prod_eq_zero hne.choose_spec rfl

theorem map_elementaryOn {S : Type*} [CommRing S] (f : R →+* S)
    {n : ℕ} (Y : Finset (Fin n)) (d : ℕ) :
    MvPolynomial.map f (elementaryOn (R := R) Y d) = elementaryOn Y d := by
  simp only [elementaryOn, map_sum, map_prod, MvPolynomial.map_X]

/-- Conjugate tail, using zero-based column indices.  The interval
`[n-m,n)` is the printed interval `n-m+1,…,n`. -/
def conjugateTail (n : ℕ) (μ : YoungDiagram) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico (n - m) n, μ.colLen j

theorem conjugateTail_mono {n m : ℕ} {μ ν : YoungDiagram} (h : μ ≤ ν) :
    conjugateTail n μ m ≤ conjugateTail n ν m := by
  apply Finset.sum_le_sum
  intro j hj
  exact YoungDiagram.colLen_le_of_le h j

/-- A generator of the untruncated Griffin ideal.  The comparison is made in
the integers so that no natural subtraction can change its mathematical content. -/
def IsElementaryGenerator (n : ℕ) (μ : YoungDiagram)
    (p : PolynomialRing n R) : Prop :=
  ∃ (Y : Finset (Fin n)) (d : ℕ), 0 < d ∧ d ≤ Y.card ∧
    (Y.card : ℤ) - (conjugateTail n μ Y.card : ℤ) < (d : ℤ) ∧
    p = elementaryOn Y d

def untruncatedIdeal (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :
    Ideal (PolynomialRing n R) := Ideal.span {p | IsElementaryGenerator n μ p}

def powerIdeal (R : Type*) [CommRing R] (n s : ℕ) :
    Ideal (PolynomialRing n R) := Ideal.span (Set.range fun i : Fin n => (X i) ^ s)

def griffinIdeal (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) (s : ℕ) :
    Ideal (PolynomialRing n R) := untruncatedIdeal R n μ ⊔ powerIdeal R n s

def springerIdeal (R : Type*) [CommRing R] (μ : YoungDiagram) :
    Ideal (PolynomialRing μ.card R) := untruncatedIdeal R μ.card μ

abbrev UntruncatedRing (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :=
  PolynomialRing n R ⧸ untruncatedIdeal R n μ

abbrev GriffinRing (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) (s : ℕ) :=
  PolynomialRing n R ⧸ griffinIdeal R n μ s

abbrev SpringerRing (R : Type*) [CommRing R] (μ : YoungDiagram) :=
  PolynomialRing μ.card R ⧸ springerIdeal R μ

theorem elementaryOn_mem_untruncatedIdeal {n : ℕ} {μ : YoungDiagram}
    (Y : Finset (Fin n)) {d : ℕ} (hd : 0 < d) (hcard : d ≤ Y.card)
    (hthreshold : (Y.card : ℤ) - (conjugateTail n μ Y.card : ℤ) < (d : ℤ)) :
    elementaryOn (R := R) Y d ∈ untruncatedIdeal R n μ :=
  Ideal.subset_span ⟨Y, d, hd, hcard, hthreshold, rfl⟩

theorem untruncatedIdeal_mono {n : ℕ} {μ ν : YoungDiagram} (h : μ ≤ ν) :
    untruncatedIdeal R n μ ≤ untruncatedIdeal R n ν := by
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hd, hcard, hthreshold, rfl⟩
  apply elementaryOn_mem_untruncatedIdeal Y hd hcard
  have htail := conjugateTail_mono (n := n) (m := Y.card) h
  exact lt_of_le_of_lt (sub_le_sub_left (by exact_mod_cast htail) _) hthreshold

theorem griffinIdeal_mono {n s : ℕ} {μ ν : YoungDiagram} (h : μ ≤ ν) :
    griffinIdeal R n μ s ≤ griffinIdeal R n ν s :=
  sup_le_sup (untruncatedIdeal_mono h) le_rfl

theorem untruncatedIdeal_le_constantCoeff_ker (n : ℕ) (μ : YoungDiagram) :
    untruncatedIdeal R n μ ≤ RingHom.ker constantCoeff := by
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hd, hcard, hthreshold, rfl⟩
  exact constantCoeff_elementaryOn Y hd

theorem powerIdeal_le_constantCoeff_ker (n : ℕ) {s : ℕ} (hs : 0 < s) :
    powerIdeal R n s ≤ RingHom.ker constantCoeff := by
  apply Ideal.span_le.mpr
  rintro p ⟨i, rfl⟩
  change constantCoeff ((X i : PolynomialRing n R) ^ s) = 0
  rw [map_pow, constantCoeff_X, zero_pow (by omega : s ≠ 0)]

theorem griffinIdeal_le_constantCoeff_ker (n : ℕ) (μ : YoungDiagram)
    {s : ℕ} (hs : 0 < s) :
    griffinIdeal R n μ s ≤ RingHom.ker constantCoeff :=
  sup_le (untruncatedIdeal_le_constantCoeff_ker n μ)
    (powerIdeal_le_constantCoeff_ker n hs)

theorem one_not_mem_griffinIdeal [Nontrivial R] (n : ℕ) (μ : YoungDiagram)
    {s : ℕ} (hs : 0 < s) : (1 : PolynomialRing n R) ∉ griffinIdeal R n μ s := by
  intro h
  have hk := griffinIdeal_le_constantCoeff_ker (R := R) n μ hs h
  simpa only [RingHom.mem_ker, map_one, one_ne_zero] using hk

/-- The literal row symmetrizer on polynomials. -/
def rowSymmetrize {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (p : PolynomialRing n R) : PolynomialRing n R :=
  ∑ ρ : G, MvPolynomial.rename (ρ : Equiv.Perm (Fin n)) p

/-- The literal column antisymmetrizer; its sign is transported from the integers. -/
def columnAlternate {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (p : PolynomialRing n R) : PolynomialRing n R :=
  ∑ σ : G, (((Equiv.Perm.sign (σ : Equiv.Perm (Fin n)) : ℤ) : R)) •
    MvPolynomial.rename (σ : Equiv.Perm (Fin n)) p

def youngApply {μ : YoungDiagram} (T : YoungTableau μ)
    (p : PolynomialRing μ.card R) : PolynomialRing μ.card R :=
  columnAlternate (colSubgroup T) (rowSymmetrize (rowSubgroup T) p)

def transportedCocharge {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (T : YoungTableau μ) : Fin μ.card →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => cochargeFilling S (T.symm i)

/-- The manuscript's unnormalized polynomial, with column alternation applied
after row symmetrization. -/
def higherSpechtPolynomial {μ : YoungDiagram} (S T : StandardYoungTableau μ) :
    PolynomialRing μ.card R :=
  youngApply T.toTableau (MvPolynomial.monomial (transportedCocharge S T.toTableau) 1)

theorem higherSpechtPolynomial_eq_sum {μ : YoungDiagram}
    (S T : StandardYoungTableau μ) :
    higherSpechtPolynomial (R := R) S T =
      ∑ σ : colSubgroup T.toTableau, ∑ ρ : rowSubgroup T.toTableau,
        (((Equiv.Perm.sign (σ : Equiv.Perm (Fin μ.card)) : ℤ) : R)) •
          MvPolynomial.rename (σ : Equiv.Perm (Fin μ.card))
            (MvPolynomial.rename (ρ : Equiv.Perm (Fin μ.card))
              (MvPolynomial.monomial (transportedCocharge S T.toTableau) 1)) := by
  simp only [higherSpechtPolynomial, youngApply, columnAlternate, rowSymmetrize,
    map_sum, Finset.smul_sum]

/-- The symmetric factor is indexed by its partition itself, padded by zeros.
Its argument is a finite weakly decreasing sequence in the final basis theorem. -/
def elementaryMultiplier (n m : ℕ) (eta : ℕ → ℕ) : PolynomialRing n R :=
  ∏ j ∈ Finset.range m,
    MvPolynomial.esymm (Fin n) R (j + 1) ^ (eta j - eta (j + 1))

@[simp] theorem rowSymmetrize_C {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (c : R) :
    rowSymmetrize G (C c) = Fintype.card G • C c := by
  simp [rowSymmetrize]

@[simp] theorem columnAlternate_bot {n : ℕ} (p : PolynomialRing n R) :
    columnAlternate (⊥ : Subgroup (Equiv.Perm (Fin n))) p = p := by
  classical
  have h (σ : (⊥ : Subgroup (Equiv.Perm (Fin n)))) :
      (σ : Equiv.Perm (Fin n)) = 1 := Subgroup.mem_bot.mp σ.property
  simp [columnAlternate, h]

/-- On a one-row tableau the unnormalized symmetrizer sends 1 to n!·1.
This equality is integral and persists in every coefficient characteristic. -/
theorem youngApply_one_of_rowSubgroup_top {μ : YoungDiagram} (T : YoungTableau μ)
    (hr : rowSubgroup T = ⊤) (hc : colSubgroup T = ⊥) :
    youngApply (R := R) T 1 = (μ.card.factorial : PolynomialRing μ.card R) := by
  rw [youngApply, hr, hc, columnAlternate_bot]
  have hcard : Fintype.card (⊤ : Subgroup (Equiv.Perm (Fin μ.card))) = μ.card.factorial := by
    rw [← Nat.card_eq_fintype_card, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
  simpa only [hcard, map_one, nsmul_eq_mul, mul_one] using
      rowSymmetrize_C (R := R) (⊤ : Subgroup (Equiv.Perm (Fin μ.card))) (1 : R)

end HigherSpecht
end
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/PrefixTableau.lean -/



/-!
# Restriction to the first labels

The shape and the restricted standard tableau are constructed from the actual
cells whose labels are less than `k`; thus the initial-prefix condition in the
Griffin indexing is not replaced by an arbitrary auxiliary tableau.
-/

noncomputable section

open Finset TauCeti

namespace HigherSpecht

theorem standardTableau_monotoneCells {μ : YoungDiagram} (S : StandardYoungTableau μ)
    {a b : ↥μ.cells} (hab : a.val ≤ b.val) : S a ≤ S b := by
  let mid : ↥μ.cells := ⟨(a.val.1, b.val.2), μ.up_left_mem hab.1 le_rfl b.property⟩
  have ham : S a ≤ S mid := by
    rcases hab.2.eq_or_lt with heq | hlt
    · have hm : a = mid := Subtype.ext (Prod.ext rfl heq)
      exact le_of_eq (congrArg S hm)
    · exact (S.row_strict hlt mid.property).le
  have hmb : S mid ≤ S b := by
    rcases hab.1.eq_or_lt with heq | hlt
    · have hm : mid = b := Subtype.ext (Prod.ext heq rfl)
      exact le_of_eq (congrArg S hm)
    · exact (S.col_strict hlt b.property).le
  exact ham.trans hmb

def prefixShape {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter fun c => if hc : c ∈ μ.cells then (S ⟨c, hc⟩).val < k else False
  isLowerSet := by
    intro b a hab hb
    obtain ⟨hbμ, hbk⟩ := Finset.mem_filter.mp hb
    have haμ : a ∈ μ.cells := μ.isLowerSet hab hbμ
    refine Finset.mem_filter.mpr ⟨haμ, ?_⟩
    have hbk' : (S ⟨b, hbμ⟩).val < k := by
      simpa only [dif_pos hbμ] using hbk
    change (if hc : a ∈ μ.cells then (S ⟨a, hc⟩).val < k else False)
    rw [dif_pos haμ]
    exact lt_of_le_of_lt
      (standardTableau_monotoneCells S (a := ⟨a, haμ⟩) (b := ⟨b, hbμ⟩) hab) hbk'

theorem mem_prefixShape {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ)
    (c : ℕ × ℕ) :
    c ∈ prefixShape S k ↔ ∃ hc : c ∈ μ.cells, (S ⟨c, hc⟩).val < k := by
  change (c ∈ μ.cells.filter _) ↔ _
  simp only [Finset.mem_filter]
  by_cases hc : c ∈ μ.cells
  · simp [hc]
  · simp [hc]

theorem prefixShape_le {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ) :
    prefixShape S k ≤ μ := by
  intro c hc
  exact ((mem_prefixShape S k c).mp hc).choose

def prefixCellEquiv {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ) :
    ↥(prefixShape S k).cells ≃ {c : ↥μ.cells // (S c).val < k} where
  toFun c := ⟨⟨c.val, prefixShape_le S k c.property⟩,
    ((mem_prefixShape S k c.val).mp c.property).choose_spec⟩
  invFun c := ⟨c.val.val, (mem_prefixShape S k c.val.val).mpr ⟨c.val.property, c.property⟩⟩
  left_inv c := rfl
  right_inv c := rfl

def initialLabelsEquiv {n k : ℕ} (hk : k ≤ n) :
    {i : Fin n // i.val < k} ≃ Fin k where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, i.isLt⟩
  left_inv i := rfl
  right_inv i := rfl

def prefixLabelEquiv {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : ↥(prefixShape S k).cells ≃ Fin k :=
  (prefixCellEquiv S k).trans
    ((S.toTableau.subtypeEquiv (fun c => Iff.rfl)).trans (initialLabelsEquiv hk))

@[simp] theorem prefixLabelEquiv_apply_val {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card)
    (c : ↥(prefixShape S k).cells) :
    (prefixLabelEquiv S k hk c).val = (S ⟨c.val, prefixShape_le S k c.property⟩).val := rfl

@[simp] theorem prefixShape_card {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card) :
    (prefixShape S k).card = k := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr (prefixLabelEquiv S k hk)

def prefixTableau {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : StandardYoungTableau (prefixShape S k) where
  toTableau := (prefixLabelEquiv S k hk).trans (finCongr (prefixShape_card S k hk).symm)
  row_strict' h hcell := by
    change (prefixLabelEquiv S k hk _).val < (prefixLabelEquiv S k hk _).val
    simp only [prefixLabelEquiv_apply_val]
    exact S.row_strict h (prefixShape_le S k hcell)
  col_strict' h hcell := by
    change (prefixLabelEquiv S k hk _).val < (prefixLabelEquiv S k hk _).val
    simp only [prefixLabelEquiv_apply_val]
    exact S.col_strict h (prefixShape_le S k hcell)

@[simp] theorem prefixTableau_apply_val {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card)
    (c : ↥(prefixShape S k).cells) :
    (prefixTableau S k hk c).val = (S ⟨c.val, prefixShape_le S k c.property⟩).val := rfl

theorem prefixShape_mono {μ : YoungDiagram} (S : StandardYoungTableau μ)
    {k l : ℕ} (hkl : k ≤ l) : prefixShape S k ≤ prefixShape S l := by
  intro c hc
  obtain ⟨hcμ, hck⟩ := (mem_prefixShape S k c).mp hc
  exact (mem_prefixShape S l c).mpr ⟨hcμ, hck.trans_le hkl⟩

@[simp] theorem prefixShape_full {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    prefixShape S μ.card = μ := by
  apply le_antisymm (prefixShape_le S _)
  intro c hc
  exact (mem_prefixShape S μ.card c).mpr ⟨hc, (S ⟨c, hc⟩).isLt⟩

@[simp] theorem prefixShape_zero {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    prefixShape S 0 = ⊥ := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcμ, hck⟩ := (mem_prefixShape S 0 c).mp hc
    exact (Nat.not_lt_zero _ hck).elim
  · exact bot_le

end HigherSpecht
end
end CanonicalSource9

section CanonicalSource10
/- Source: HigherSpecht/Statements.lean -/



/-!
# Exact polynomial-basis targets

These are propositions describing the literal polynomial families, not
assertions that they have been proved.  Catabolism eligibility uses the actual
terminating insertion relation; the termination and recursive-catabolism
correspondence are separate outstanding dependencies.  The representation,
fiber, and canonical-module conclusions require further target interfaces and
are not silently folded into these vector-space basis propositions.
-/

noncomputable section

open TauCeti MvPolynomial Module

namespace HigherSpecht

structure StandardPair (n : ℕ) where
  shape : YoungDiagram
  card_eq : shape.card = n
  left : StandardYoungTableau shape
  right : StandardYoungTableau shape

def pairPolynomial {R : Type*} [CommRing R] {n : ℕ} (P : StandardPair n) :
    PolynomialRing n R :=
  MvPolynomial.rename (finCongr P.card_eq)
    (higherSpechtPolynomial P.left P.right)

def prefixEligible {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (P : StandardPair n) : Prop :=
  CatDominates (prefixTableau P.left lam.card (by simpa only [P.card_eq] using hk)) lam

abbrev SpringerIndex (lam : YoungDiagram) :=
  {P : StandardPair lam.card // CatDominates P.left lam}

def springerFamily (R : Type*) [CommRing R] (lam : YoungDiagram) :
    SpringerIndex lam → SpringerRing R lam :=
  fun i => Ideal.Quotient.mk (springerIdeal R lam) (pairPolynomial i.val)

structure GriffinIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) where
  pair : StandardPair n
  multiplier : YoungDiagram
  eligible : prefixEligible lam hk pair
  descents_lt : descentNumber pair.left < s
  multiplier_length : multiplier.colLen 0 ≤ n - lam.card
  multiplier_width : multiplier.rowLen 0 ≤ s - descentNumber pair.left - 1

def griffinPolynomial {R : Type*} [CommRing R] {n : ℕ} {lam : YoungDiagram}
    {hk : lam.card ≤ n} {s : ℕ} (i : GriffinIndex n lam hk s) : PolynomialRing n R :=
  pairPolynomial i.pair * elementaryMultiplier n (n - lam.card) i.multiplier.rowLen

def griffinFamily (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    GriffinIndex n lam hk s → GriffinRing R n lam s :=
  fun i => Ideal.Quotient.mk (griffinIdeal R n lam s) (griffinPolynomial i)

abbrev UntruncatedIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :=
  {P : StandardPair n // prefixEligible lam hk P}

def untruncatedFamily (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) : UntruncatedIndex n lam hk → UntruncatedRing R n lam :=
  fun i => Ideal.Quotient.mk (untruncatedIdeal R n lam) (pairPolynomial i.val)

structure UntruncatedVectorIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) where
  base : UntruncatedIndex n lam hk
  multiplier : YoungDiagram
  multiplier_length : multiplier.colLen 0 ≤ n - lam.card

def untruncatedVectorFamily (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) : UntruncatedVectorIndex n lam hk → UntruncatedRing R n lam :=
  fun i => Ideal.Quotient.mk (untruncatedIdeal R n lam)
    (pairPolynomial i.base.val * elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)

/-- A basis assertion retaining the prescribed vector at every actual index. -/
def IsSpecifiedBasis {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (v : ι → V) : Prop :=
  ∃ b : Basis ι R V, ∀ i, b i = v i

def SpringerBasisTarget (R : Type*) [Field R] : Prop :=
  ∀ lam : YoungDiagram, IsSpecifiedBasis (R := R) (springerFamily R lam)

def GriffinBasisTarget (R : Type*) [Field R] : Prop :=
  ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ),
    0 < lam.card → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s)

/-- The degreewise-stabilized vector-space statement preceding the free-module
assertion in Section 6.1.  The empty partition is included. -/
def UntruncatedVectorBasisTarget (R : Type*) [Field R] : Prop :=
  ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    IsSpecifiedBasis (R := R) (untruncatedVectorFamily R n lam hk)

/-- The basis portion of Corollary 8.1, with the exact field characteristic
range; the associated irreducible-module assertions are separate conclusions. -/
def GriffinCharacteristicTarget (R : Type*) [Field R] : Prop :=
  ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ),
    0 < lam.card → lam.colLen 0 ≤ s →
      (IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s) ↔ ringChar R = 0 ∨ n < ringChar R)

def SpringerCharacteristicTarget (R : Type*) [Field R] : Prop :=
  ∀ lam : YoungDiagram,
    (IsSpecifiedBasis (R := R) (springerFamily R lam) ↔ ringChar R = 0 ∨ lam.card < ringChar R)

end HigherSpecht
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/SmallCharacteristic.lean -/



/-!
# The small-characteristic obstruction for the specified family

The paper uses unnormalized Young operators.  Its one-row, empty-multiplier
candidate is therefore `n!`, not `1`.  This gives the necessary characteristic
restriction in Corollary 8.1 without any dimension or semisimplicity input.
This file does not assert the converse basis theorem.
-/

noncomputable section

open TauCeti TauCeti.YoungTableau MvPolynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R]

theorem tableauRows_eq_zero_of_one_row {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (hμ : μ.colLen 0 ≤ 1) : tableauRows S = 0 := by
  funext i
  unfold tableauRows
  split_ifs with hi
  · exact rowIndex_eq_zero_of_colLen_le_one S.toTableau hμ _
  · rfl

theorem cochargeLabel_eq_zero_of_one_row {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (hμ : μ.colLen 0 ≤ 1) (i : Fin μ.card) :
    cochargeLabel S i = 0 := by
  simp [cochargeLabel, tableauRows_eq_zero_of_one_row S hμ, ascentCount]

theorem transportedCocharge_eq_zero_of_one_row {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (T : YoungTableau μ) (hμ : μ.colLen 0 ≤ 1) :
    transportedCocharge S T = 0 := by
  ext i
  simp [transportedCocharge, cochargeFilling, cochargeLabel_eq_zero_of_one_row S hμ]

theorem higherSpechtPolynomial_one_row {μ : YoungDiagram}
    (S T : StandardYoungTableau μ) (hμ : μ.colLen 0 ≤ 1) :
    higherSpechtPolynomial (R := R) S T = (μ.card.factorial : PolynomialRing μ.card R) := by
  have hr := (rowSubgroup_eq_top_iff T.toTableau).mpr hμ
  rw [higherSpechtPolynomial, transportedCocharge_eq_zero_of_one_row S T.toTableau hμ,
    ← MvPolynomial.one_def]
  exact youngApply_one_of_rowSubgroup_top T.toTableau hr
    (colSubgroup_eq_bot_of_rowSubgroup_eq_top T.toTableau hr)

theorem higherSpechtPolynomial_one_row_eq_zero {p : ℕ} [CharP R p]
    (hp : 0 < p) {μ : YoungDiagram} (S T : StandardYoungTableau μ)
    (hμ : μ.colLen 0 ≤ 1) (hpn : p ≤ μ.card) :
    higherSpechtPolynomial (R := R) S T = 0 := by
  rw [higherSpechtPolynomial_one_row S T hμ]
  have hz : (μ.card.factorial : R) = 0 :=
    (CharP.cast_eq_zero_iff R p μ.card.factorial).mpr (Nat.dvd_factorial hp hpn)
  simpa only [map_natCast, map_zero] using congrArg (C : R →+* PolynomialRing μ.card R) hz

/-- A family containing this literal one-row candidate is dependent in every
positive characteristic at most the number of variables. -/
theorem not_linearIndependent_of_contains_one_row
    {p : ℕ} [CharP R p] [Nontrivial R] (hp : 0 < p)
    {μ : YoungDiagram} (S T : StandardYoungTableau μ)
    (hμ : μ.colLen 0 ≤ 1) (hpn : p ≤ μ.card)
    {ι : Type*} (v : ι → PolynomialRing μ.card R) (i : ι)
    (hi : v i = higherSpechtPolynomial S T) : ¬ LinearIndependent R v := by
  intro hv
  exact hv.ne_zero i (hi.trans (higherSpechtPolynomial_one_row_eq_zero hp S T hμ hpn))

/-- The same obstruction survives quotienting by the actual Griffin ideal.
In particular quotient relations cannot repair the zero basis vector. -/
theorem not_linearIndependent_quotient_of_contains_one_row
    {p : ℕ} [CharP R p] [Nontrivial R] (hp : 0 < p)
    {μ : YoungDiagram} (S T : StandardYoungTableau μ)
    (hμ : μ.colLen 0 ≤ 1) (hpn : p ≤ μ.card)
    (lam : YoungDiagram) (s : ℕ)
    {ι : Type*} (v : ι → PolynomialRing μ.card R) (i : ι)
    (hi : v i = higherSpechtPolynomial S T) :
    ¬ LinearIndependent R (fun j =>
      Ideal.Quotient.mk (griffinIdeal R μ.card lam s) (v j)) := by
  intro hv
  apply hv.ne_zero i
  rw [hi, higherSpechtPolynomial_one_row_eq_zero hp S T hμ hpn, map_zero]

end HigherSpecht
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/OneRowIndex.lean -/



/-!
# The actual one-row index and characteristic obstruction

The zero cocharge word is run through the genuine insertion algorithm.  Its
output dominates every diagram of the appropriate size.  Consequently the
factorial vector is an actual member of each prescribed family, not a presumed
member of an unspecified family.
-/

noncomputable section

open Finset TauCeti MvPolynomial

namespace HigherSpecht

def oneRowShape (n : ℕ) : YoungDiagram where
  cells := {0} ×ˢ Finset.range n
  isLowerSet := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at h ⊢
    exact ⟨by omega, hbd.trans_lt h.2⟩

@[simp] theorem oneRowShape_card (n : ℕ) : (oneRowShape n).card = n := by
  simp [oneRowShape, YoungDiagram.card]

@[simp] theorem mem_oneRowShape (n : ℕ) (c : ℕ × ℕ) :
    c ∈ oneRowShape n ↔ c.1 = 0 ∧ c.2 < n := by
  change c ∈ ({0} ×ˢ Finset.range n) ↔ _
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]

@[simp] theorem oneRowShape_rowLen (n r : ℕ) :
    (oneRowShape n).rowLen r = if r = 0 then n else 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_oneRowShape]
  by_cases hr : r = 0 <;> simp [hr]

theorem oneRowShape_colLen_le_one (n : ℕ) : (oneRowShape n).colLen 0 ≤ 1 := by
  by_contra h
  have hm : (1, 0) ∈ oneRowShape n := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  simp at hm

@[simp] theorem oneRowShape_zero : oneRowShape 0 = ⊥ := by
  ext c
  simp

lemma oneRowShape_add (n : ℕ) :
    (oneRowShape n).addCell (0, (oneRowShape n).rowLen 0) = oneRowShape (n + 1) := by
  ext ⟨a, b⟩
  change (a, b) ∈ (oneRowShape n).addCell (0, (oneRowShape n).rowLen 0) ↔
    (a, b) ∈ oneRowShape (n + 1)
  simp only [YoungDiagram.mem_addCell, oneRowShape_rowLen, if_pos rfl,
    mem_oneRowShape, Prod.le_def, ite_true]
  omega

lemma catRun_replicate_zero (m n : ℕ) :
    catRun m ⟨List.replicate m 0, oneRowShape n⟩ = ⟨[], oneRowShape (n + m)⟩ := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    have hadd : YoungDiagram.IsAddable (oneRowShape n) (0, (oneRowShape n).rowLen 0) := by
      rw [YoungDiagram.isAddable_iff_rowLen]
      exact ⟨rfl, fun i hi => by omega⟩
    have hstep : catRun 1 ⟨List.replicate (m + 1) 0, oneRowShape n⟩ =
        ⟨List.replicate m 0, oneRowShape (n + 1)⟩ := by
      change catStep ⟨List.replicate (m + 1) 0, oneRowShape n⟩ = _
      unfold catStep
      rw [List.reverse_replicate, List.replicate_succ]
      dsimp only
      rw [if_pos hadd, List.reverse_replicate, oneRowShape_add]
    rw [catRun_add, hstep, ih]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem catWordOutput_replicate_zero (n : ℕ) :
    CatWordOutput (List.replicate n 0) (oneRowShape n) := by
  refine ⟨n, ?_⟩
  simpa only [oneRowShape_zero, Nat.zero_add] using catRun_replicate_zero n 0

theorem cochargeWord_one_row {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (hμ : μ.colLen 0 ≤ 1) : cochargeWord S = List.replicate μ.card 0 := by
  have hmap : (rowReadingCells μ).map (cochargeFilling S) =
      (rowReadingCells μ).map (fun _ => 0) := by
    apply List.map_congr_left
    intro c hc
    exact cochargeLabel_eq_zero_of_one_row S hμ (S c)
  rw [cochargeWord, hmap, List.map_const']
  simp [rowReadingCells, YoungDiagram.card]

theorem oneRowShape_dominates {n : ℕ} (μ : YoungDiagram) (hμ : μ.card ≤ n) :
    Dominates (oneRowShape n) μ := by
  intro r
  by_cases hr : r = 0
  · simp [hr]
  · have hleft : (∑ i ∈ Finset.range r, μ.rowLen i) ≤ μ.card := by
      rw [YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
      exact Finset.card_filter_le _ _
    have hright : (∑ i ∈ Finset.range r, (oneRowShape n).rowLen i) = n := by
      simp only [oneRowShape_rowLen]
      rw [Finset.sum_ite_eq']
      simp [Nat.pos_of_ne_zero hr]
    rw [hright]
    exact hleft.trans hμ

theorem catDominates_one_row {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (hμ : μ.colLen 0 ≤ 1) (lam : YoungDiagram) (hcard : lam.card ≤ μ.card) :
    CatDominates S lam := by
  refine ⟨oneRowShape μ.card, ?_, oneRowShape_dominates lam hcard⟩
  change CatWordOutput (cochargeWord S) _
  rw [cochargeWord_one_row S hμ]
  exact catWordOutput_replicate_zero _

def oneRowPair (n : ℕ) : StandardPair n where
  shape := oneRowShape n
  card_eq := oneRowShape_card n
  left := StandardYoungTableau.rowSuperstandard (oneRowShape n)
  right := StandardYoungTableau.rowSuperstandard (oneRowShape n)

theorem pairPolynomial_oneRow {R : Type*} [CommRing R] (n : ℕ) :
    pairPolynomial (R := R) (oneRowPair n) = (n.factorial : PolynomialRing n R) := by
  unfold pairPolynomial oneRowPair
  rw [higherSpechtPolynomial_one_row _ _ (oneRowShape_colLen_le_one n), map_natCast,
    oneRowShape_card]

def oneRowSpringerIndex (lam : YoungDiagram) : SpringerIndex lam :=
  ⟨oneRowPair lam.card, catDominates_one_row _ (oneRowShape_colLen_le_one _) lam
    (by simp [oneRowPair])⟩

def oneRowGriffinIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) : GriffinIndex n lam hk s where
  pair := oneRowPair n
  multiplier := ⊥
  eligible := by
    apply catDominates_one_row
    · exact (YoungDiagram.colLen_le_of_le (prefixShape_le _ _) 0).trans
        (oneRowShape_colLen_le_one n)
    · exact le_of_eq (prefixShape_card (oneRowPair n).left lam.card
        (by simpa only [oneRowPair, oneRowShape_card] using hk)).symm
  descents_lt := by
    simpa [descentNumber, oneRowPair,
      tableauRows_eq_zero_of_one_row _ (oneRowShape_colLen_le_one n), ascentCount] using hs
  multiplier_length := by simp
  multiplier_width := by simp

theorem griffinPolynomial_oneRow {R : Type*} [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) :
    griffinPolynomial (R := R) (oneRowGriffinIndex n lam hk s hs) =
      (n.factorial : PolynomialRing n R) := by
  simp [griffinPolynomial, oneRowGriffinIndex, pairPolynomial_oneRow, elementaryMultiplier]

/-- The necessary characteristic restriction for the full specified Springer
family, for every partition. -/
theorem not_springerBasis_of_small_characteristic {R : Type*} [Field R]
    {p : ℕ} [CharP R p] (hp : 0 < p) (lam : YoungDiagram) (hpn : p ≤ lam.card) :
    ¬ IsSpecifiedBasis (R := R) (springerFamily R lam) := by
  rintro ⟨B, hB⟩
  have hzero : springerFamily R lam (oneRowSpringerIndex lam) = 0 := by
    rw [springerFamily, oneRowSpringerIndex, pairPolynomial_oneRow, map_natCast]
    have hz : (lam.card.factorial : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).mpr (Nat.dvd_factorial hp hpn)
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R (SpringerRing R lam)) hz
  exact B.linearIndependent.ne_zero (oneRowSpringerIndex lam)
    ((hB _).trans hzero)

/-- The necessary characteristic restriction for every full Griffin family;
all its prescribed parameters and all its actual indices are retained. -/
theorem not_griffinBasis_of_small_characteristic {R : Type*} [Field R]
    {p : ℕ} [CharP R p] (hp : 0 < p) (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hs : 0 < s) (hpn : p ≤ n) :
    ¬ IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s) := by
  rintro ⟨B, hB⟩
  let i := oneRowGriffinIndex n lam hk s hs
  have hzero : griffinFamily R n lam hk s i = 0 := by
    rw [griffinFamily, griffinPolynomial_oneRow, map_natCast]
    have hz : (n.factorial : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).mpr (Nat.dvd_factorial hp hpn)
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R (GriffinRing R n lam s)) hz
  exact B.linearIndependent.ne_zero i ((hB i).trans hzero)

end HigherSpecht
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/CatFirstRow.lean -/



/-!
# Removing a completed first row from the actual insertion machine

This is the dynamical step in the greedy catabolism recursion.  A first row
of length `m` does not alter the shifted tail execution provided the remaining
zero letters and the already filled first tail row together number at most
`m`.  The capacity is an invariant of the literal one-step algorithm.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

def prependRowFunction (m : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => r j

@[simp] theorem prependRowFunction_zero (m : ℕ) (r : ℕ → ℕ) :
    prependRowFunction m r 0 = m := rfl

@[simp] theorem prependRowFunction_succ (m : ℕ) (r : ℕ → ℕ) (j : ℕ) :
    prependRowFunction m r (j + 1) = r j := rfl

def liftRawCat (m : ℕ) (s : RawCatState) : RawCatState :=
  (s.1.map Nat.succ, prependRowFunction m s.2)

def FirstRowCapacity (m : ℕ) (s : RawCatState) : Prop :=
  s.2 0 + s.1.count 0 ≤ m

theorem prependRowFunction_update (m : ℕ) (r : ℕ → ℕ) (a b : ℕ) :
    prependRowFunction m (Function.update r a b) =
      Function.update (prependRowFunction m r) (a + 1) b := by
  funext j
  cases j with
  | zero => simp [Function.update_apply]
  | succ j => simp [Function.update_apply]

theorem rawCanInsert_prependRowFunction {m : ℕ} {r : ℕ → ℕ} {a : ℕ}
    (hzero : a = 0 → r 0 < m) :
    rawCanInsert (prependRowFunction m r) (a + 1) ↔ rawCanInsert r a := by
  cases a with
  | zero => simp [rawCanInsert, hzero rfl]
  | succ a => simp [rawCanInsert, Nat.add_sub_cancel]

theorem firstRowCapacity_step {m : ℕ} {s : RawCatState}
    (hs : FirstRowCapacity m s) : FirstRowCapacity m (rawCatStep s) := by
  rcases s with ⟨w, r⟩
  induction w using List.reverseRecOn with
  | nil => exact hs
  | append_singleton w a ih =>
    rw [rawCatStep_append, rawCatPresent]
    by_cases ha : rawCanInsert r a
    · rw [if_pos ha]
      by_cases ha0 : a = 0
      · subst a
        simpa [FirstRowCapacity, List.count_append, Function.update_apply,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      · simpa [FirstRowCapacity, List.count_append, Function.update_apply, ha0,
          Ne.symm ha0] using hs
    · rw [if_neg ha]
      have ha0 : a ≠ 0 := fun h => ha (Or.inl h)
      simpa [FirstRowCapacity, List.count_append, ha0, Ne.symm ha0] using hs

theorem rawCatStep_liftRawCat {m : ℕ} {s : RawCatState}
    (hs : FirstRowCapacity m s) :
    rawCatStep (liftRawCat m s) = liftRawCat m (rawCatStep s) := by
  rcases s with ⟨w, r⟩
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    have hz : a = 0 → r 0 < m := by
      intro ha
      subst a
      simp only [FirstRowCapacity, List.count_append, List.count_singleton_self] at hs
      omega
    have hcan := rawCanInsert_prependRowFunction hz
    simp only [liftRawCat, List.map_append, List.map_singleton, rawCatStep_append,
      rawCatPresent]
    by_cases ha : rawCanInsert r a
    · rw [if_pos ha, if_pos (hcan.mpr ha)]
      exact Prod.ext rfl (prependRowFunction_update m r a (r a + 1)).symm
    · rw [if_neg ha, if_neg (fun h => ha (hcan.mp h))]
      rfl

theorem firstRowCapacity_run {m : ℕ} {s : RawCatState}
    (hs : FirstRowCapacity m s) (N : ℕ) : FirstRowCapacity m (rawCatRun N s) := by
  induction N with
  | zero => exact hs
  | succ N ih =>
    simpa only [rawCatRun, Function.iterate_succ_apply'] using firstRowCapacity_step ih

theorem rawCatRun_liftRawCat {m : ℕ} {s : RawCatState}
    (hs : FirstRowCapacity m s) (N : ℕ) :
    rawCatRun N (liftRawCat m s) = liftRawCat m (rawCatRun N s) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simpa only [rawCatRun, Function.iterate_succ_apply'] using
      (congrArg rawCatStep ih).trans (rawCatStep_liftRawCat (firstRowCapacity_run hs N))

/-- The comparison is stated on the actual Young-diagram machine.  Its
conclusion gives every row of the final output, not an unspecified output
or a replacement definition of catabolizability. -/
theorem catRun_firstRow_lift {w : List ℕ} {nu : YoungDiagram} {m N : ℕ}
    (hcount : w.count 0 ≤ m)
    (hout : catRun N ⟨w, ⊥⟩ = ⟨[], nu⟩) :
    (catRun N ⟨w.map Nat.succ, oneRowShape m⟩).word = [] ∧
      (catRun N ⟨w.map Nat.succ, oneRowShape m⟩).shape.rowLen =
        prependRowFunction m nu.rowLen := by
  have hcap : FirstRowCapacity m (catEncoding ⟨w, ⊥⟩) := by
    simpa [FirstRowCapacity, catEncoding] using hcount
  have hstart : liftRawCat m (catEncoding ⟨w, ⊥⟩) =
      catEncoding ⟨w.map Nat.succ, oneRowShape m⟩ := by
    change (w.map Nat.succ, prependRowFunction m (⊥ : YoungDiagram).rowLen) =
      (w.map Nat.succ, (oneRowShape m).rowLen)
    apply Prod.ext
    · rfl
    · funext j
      cases j <;> simp [liftRawCat, catEncoding, prependRowFunction, oneRowShape_rowLen]
  have hr := rawCatRun_liftRawCat hcap N
  rw [hstart, ← catEncoding_run, ← catEncoding_run, hout] at hr
  exact ⟨congrArg Prod.fst hr, congrArg Prod.snd hr⟩

end HigherSpecht
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/CatGreedyWord.lean -/



/-!
# The literal first greedy catabolism phase

The positive tail of the bottom row is corotated, the zero interval is
inserted, and the remaining alphabet is lowered by one.  This file proves
the exact execution and output-row formulas; identifying the lowered word
with the cocharge word of the catabolized standard tableau is a separate
combinatorial step.
-/

noncomputable section

open TauCeti Function

namespace HigherSpecht

theorem catRun_corotate_positive_tail (before tail : List ℕ)
    (hpos : ∀ a ∈ tail, 0 < a) :
    catRun tail.length ⟨before ++ tail, ⊥⟩ =
      ⟨tail.map Nat.succ ++ before, ⊥⟩ := by
  induction tail using List.reverseRecOn generalizing before with
  | nil => simp
  | append_singleton tail a ih =>
    have ha : 0 < a := hpos a (by simp)
    have htail : ∀ b ∈ tail, 0 < b := fun b hb => hpos b (by simp [hb])
    have hnot : ¬ YoungDiagram.IsAddable (⊥ : YoungDiagram) (a, (⊥ : YoungDiagram).rowLen a) := by
      rw [isAddable_rowEnd_iff]
      simp [rawCanInsert, Nat.ne_of_gt ha]
    rw [List.length_append, List.length_singleton, catRun_add]
    change catRun tail.length (catStep ⟨before ++ (tail ++ [a]), ⊥⟩) = _
    rw [← List.append_assoc, catStep_append, if_neg hnot]
    rw [show (a + 1) :: (before ++ tail) = ((a + 1) :: before) ++ tail by rfl,
      ih _ htail]
    simp only [List.map_append, List.map_singleton, List.append_assoc, List.singleton_append]

theorem catRun_insert_zero_tail (before : List ℕ) (m n : ℕ) :
    catRun m ⟨before ++ List.replicate m 0, oneRowShape n⟩ =
      ⟨before, oneRowShape (n + m)⟩ := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    have hadd : YoungDiagram.IsAddable (oneRowShape n) (0, (oneRowShape n).rowLen 0) := by
      rw [isAddable_rowEnd_iff]
      exact Or.inl rfl
    have hstep : catRun 1 ⟨before ++ List.replicate (m + 1) 0, oneRowShape n⟩ =
        ⟨before ++ List.replicate m 0, oneRowShape (n + 1)⟩ := by
      change catStep _ = _
      rw [List.replicate_succ', ← List.append_assoc, catStep_append, if_pos hadd,
        oneRowShape_add]
    rw [catRun_add, hstep, ih]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem catRun_greedy_first_phase (upper bottom : List ℕ) (m : ℕ)
    (hbottom : ∀ a ∈ bottom, 0 < a) :
    catRun (m + bottom.length) ⟨upper ++ List.replicate m 0 ++ bottom, ⊥⟩ =
      ⟨bottom.map Nat.succ ++ upper, oneRowShape m⟩ := by
  rw [catRun_add, catRun_corotate_positive_tail _ bottom hbottom]
  rw [← List.append_assoc, ← oneRowShape_zero]
  simpa only [Nat.zero_add] using
    catRun_insert_zero_tail (bottom.map Nat.succ ++ upper) m 0

theorem succ_map_pred_of_positive (w : List ℕ) (hpos : ∀ a ∈ w, 0 < a) :
    (w.map Nat.pred).map Nat.succ = w := by
  rw [List.map_map]
  calc
    w.map (Nat.succ ∘ Nat.pred) = w.map id := by
      apply List.map_congr_left
      intro a ha
      exact Nat.succ_pred_eq_of_pos (hpos a ha)
    _ = w := List.map_id w

def greedyTailWord (upper bottom : List ℕ) : List ℕ := bottom ++ upper.map Nat.pred

theorem greedyTailWord_succ (upper bottom : List ℕ)
    (hupper : ∀ a ∈ upper, 0 < a) :
    (greedyTailWord upper bottom).map Nat.succ = bottom.map Nat.succ ++ upper := by
  rw [greedyTailWord, List.map_append, succ_map_pred_of_positive upper hupper]

/-- Exact row-by-row greedy recursion, from genuine terminating runs of both
words.  It is valid before any appeal to standard tableaux or RSK. -/
theorem catWordOutput_greedy_rows (upper bottom : List ℕ) (m : ℕ)
    (hupper : ∀ a ∈ upper, 0 < a) (hbottom : ∀ a ∈ bottom, 0 < a)
    (hcapacity : (greedyTailWord upper bottom).count 0 ≤ m)
    {nu tail : YoungDiagram}
    (hnu : CatWordOutput (upper ++ List.replicate m 0 ++ bottom) nu)
    (htail : CatWordOutput (greedyTailWord upper bottom) tail) :
    nu.rowLen = prependRowFunction m tail.rowLen := by
  obtain ⟨N, hN⟩ := htail
  have hlift := catRun_firstRow_lift hcapacity hN
  rw [greedyTailWord_succ upper bottom hupper] at hlift
  let result := catRun N ⟨bottom.map Nat.succ ++ upper, oneRowShape m⟩
  have hresult : result = ⟨[], result.shape⟩ := CatState.ext hlift.1 rfl
  have hout : CatWordOutput (upper ++ List.replicate m 0 ++ bottom) result.shape := by
    refine ⟨N + (m + bottom.length), ?_⟩
    rw [catRun_add, catRun_greedy_first_phase upper bottom m hbottom]
    exact hresult
  rw [catWordOutput_unique hnu hout]
  exact hlift.2

end HigherSpecht
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/RSKIndices.lean -/



/-!
# The literal pair index and the verified RSK correspondence

The paper indexes higher Specht polynomials by a diagram and two standard
tableaux.  Tau Ceti's RSK correspondence indexes the same pair by a partition
of the ambient integer.  The equivalences here remove that representation
difference, and retain the actual insertion and recording tableaux.

No catabolizability claim is inferred merely from this equivalence.  Its
restriction to eligible tableaux is stated with the eligibility predicate
on the actual insertion tableau.
-/

noncomputable section

open TauCeti

namespace HigherSpecht

def standardPairSigmaEquiv (n : ℕ) : StandardPair n ≃
    Σ μ : {μ : YoungDiagram | μ.card = n},
      StandardYoungTableau μ.val × StandardYoungTableau μ.val where
  toFun P := ⟨⟨P.shape, P.card_eq⟩, P.left, P.right⟩
  invFun x := ⟨x.1.val, x.1.property, x.2.1, x.2.2⟩
  left_inv P := by cases P; rfl
  right_inv x := by rcases x with ⟨⟨μ, hμ⟩, S, T⟩; rfl

def standardPairPartitionEquiv (n : ℕ) : StandardPair n ≃
    Σ μ : n.Partition,
      StandardYoungTableau (YoungDiagram.ofPartition μ) ×
        StandardYoungTableau (YoungDiagram.ofPartition μ) :=
  (standardPairSigmaEquiv n).trans (Equiv.sigmaCongrLeft' YoungDiagram.equivPartition)

def rskPair (n : ℕ) : Equiv.Perm (Fin n) ≃ StandardPair n :=
  (TauCeti.rsk n).trans (standardPairPartitionEquiv n).symm

@[simp] theorem rskPair_shape (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (rskPair n σ).shape = YoungDiagram.ofPartition (TauCeti.rsk n σ).1 := rfl

@[simp] theorem rskPair_left (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (rskPair n σ).left = (TauCeti.rsk n σ).2.1 := rfl

@[simp] theorem rskPair_right (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (rskPair n σ).right = (TauCeti.rsk n σ).2.2 := rfl

theorem rskPair_left_rows (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (rskPair n σ).left.toRows.map (List.map Fin.val) =
      (TauCeti.robinsonSchensted (List.ofFn σ)).1.map (List.map Fin.val) :=
  σ.map_val_toRows_rsk_apply

theorem rskPair_recording_word (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (rskPair n σ).right.rowWord =
      (TauCeti.robinsonSchensted (List.ofFn σ)).2 :=
  σ.rowWord_rsk_apply

noncomputable instance instFintypeStandardPair (n : ℕ) : Fintype (StandardPair n) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n)) (rskPair n)

theorem card_standardPair (n : ℕ) : Fintype.card (StandardPair n) = n.factorial := by
  rw [← Fintype.card_congr (rskPair n), Fintype.card_perm, Fintype.card_fin]

def rskEligibleEquiv (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    {σ : Equiv.Perm (Fin n) | prefixEligible lam hk (rskPair n σ)} ≃
      UntruncatedIndex n lam hk :=
  (rskPair n).subtypeEquiv (fun σ => Iff.rfl)

theorem card_untruncatedIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Nat.card (UntruncatedIndex n lam hk) =
      Nat.card {σ : Equiv.Perm (Fin n) | prefixEligible lam hk (rskPair n σ)} :=
  Nat.card_congr (rskEligibleEquiv n lam hk).symm

end HigherSpecht
end
end CanonicalSource15
