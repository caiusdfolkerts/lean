module
public import Papers.RationalityTenBasisFamilies
public import Papers.RationalityTenSatCircuit
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.BooleanAlgebra

@[expose] public section

/-!
# Semantic coverage of a one-element basis extension

Every clause has one of four mathematical reasons: a known old basis,
basis exchange, the new element being a nonloop, or exclusion of one
explicit candidate extension. A refutation therefore proves that every
actual basis family extending the old family matches a candidate.
Neither the catalogue nor an untrusted SAT run is assumed complete.
-/

noncomputable section
namespace Papers.RationalityTen.BasisExtensionCNF

open Finset BasisFamilies
abbrev Point := Fin 8

noncomputable instance literalDecidableEq : DecidableEq Sat.Literal := fun a b =>
  match a,b with
  | .pos i,.pos j => decidable_of_iff (i=j) (by constructor <;> intro h <;> cases h <;> rfl)
  | .neg i,.neg j => decidable_of_iff (i=j) (by constructor <;> intro h <;> cases h <;> rfl)
  | .pos _,.neg _ => isFalse (by intro h; cases h)
  | .neg _,.pos _ => isFalse (by intro h; cases h)

theorem satisfies_of_true_literal (v : Sat.Valuation) (c : List Sat.Literal)
    (l : Sat.Literal) (hl : l ∈ c) (ht : ¬v.neg l) : v.satisfies c := by
  induction c with
  | nil => exact False.elim (List.not_mem_nil hl)
  | cons a cs ih =>
    intro ha
    rcases List.mem_cons.mp hl with rfl | hl
    · exact False.elim (ht ha)
    · exact ih hl

inductive Origin (k l : ℕ) where
  | fixed (i : Fin k)
  | exchange (left right : Fin k) (removed : Point)
  | newPoint
  | excluded (model : Fin l)
  deriving DecidableEq

variable {k t l : ℕ}

def basisValuation {ground : Finset Point} {rank : ℕ}
    (M : BasisFamily ground rank) (U : Fin k → Finset Point) : Sat.Valuation :=
  fun i => ∃ hi : i < k, U ⟨i,hi⟩ ∈ M.bases

theorem basisValuation_at {ground : Finset Point} {rank : ℕ}
    (M : BasisFamily ground rank) (U : Fin k → Finset Point) (i : Fin k) :
    basisValuation M U i.val ↔ U i ∈ M.bases := by
  constructor
  · rintro ⟨hi,h⟩
    exact h
  · exact fun h => ⟨i.isLt,h⟩

def ModelMatch {ground : Finset Point} {rank : ℕ}
    (M : BasisFamily ground rank) (U : Fin k → Finset Point)
    (newIndex : Fin t → Fin k) (code : ℕ) : Prop :=
  ∀ j : Fin t, U (newIndex j) ∈ M.bases ↔ code.testBit j.val = true

def ValidOrigin (U : Fin k → Finset Point) (e : Point)
    (old : Finset (Finset Point)) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) : Origin k l → List Sat.Literal → Prop
  | .fixed i,c => e ∉ U i ∧
      (if U i ∈ old then Sat.Literal.pos i.val else Sat.Literal.neg i.val) ∈ c
  | .exchange a b x,c =>
      x ∈ U a ∧ x ∉ U b ∧ Sat.Literal.neg a.val ∈ c ∧ Sat.Literal.neg b.val ∈ c ∧
      ∀ y ∈ U b, y ∉ U a → ∃ i : Fin k,
        U i = insert y ((U a).erase x) ∧ Sat.Literal.pos i.val ∈ c
  | .newPoint,c => ∀ i : Fin k, e ∈ U i → Sat.Literal.pos i.val ∈ c
  | .excluded w,c => ∀ j : Fin t,
      (if (models w).testBit j.val then Sat.Literal.neg (newIndex j).val
       else Sat.Literal.pos (newIndex j).val) ∈ c

instance (U : Fin k → Finset Point) (e : Point)
    (old : Finset (Finset Point)) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal) :
    Decidable (ValidOrigin U e old newIndex models o c) := by
  cases o <;> unfold ValidOrigin <;> infer_instance

theorem origin_sound {ground : Finset Point} {rank : ℕ}
    (M : BasisFamily ground rank) (U : Fin k → Finset Point) (e : Point)
    (old : Finset (Finset Point)) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ)
    (hcomplete : ∀ A ∈ M.bases, ∃ i : Fin k, U i = A)
    (he : e ∈ ground)
    (hold : ∀ i : Fin k, e ∉ U i → (U i ∈ M.bases ↔ U i ∈ old))
    (hnone : ∀ w, ¬ModelMatch M U newIndex (models w))
    (o : Origin k l) (c : List Sat.Literal)
    (hvalid : ValidOrigin U e old newIndex models o c) :
    (basisValuation M U).satisfies c := by
  classical
  cases o with
  | fixed i =>
    obtain ⟨hei,hlit⟩ := hvalid
    by_cases hi : U i ∈ old
    · have hm := (hold i hei).mpr hi
      apply satisfies_of_true_literal _ c (.pos i.val) (by simpa [hi] using hlit)
      exact fun h => h ((basisValuation_at M U i).mpr hm)
    · apply satisfies_of_true_literal _ c (.neg i.val) (by simpa [hi] using hlit)
      exact fun h => hi ((hold i hei).mp ((basisValuation_at M U i).mp h))
  | exchange a b x =>
    obtain ⟨hxa,hxb,hla,hlb,hy⟩ := hvalid
    by_cases ha : U a ∈ M.bases
    · by_cases hb : U b ∈ M.bases
      · obtain ⟨y,hyb,hya,hnew⟩ := M.exchange (U a) ha (U b) hb x hxa hxb
        obtain ⟨i,hi,hli⟩ := hy y hyb hya
        apply satisfies_of_true_literal _ c (.pos i.val) hli
        intro h
        apply h
        apply (basisValuation_at M U i).mpr
        exact hi.symm ▸ hnew
      · apply satisfies_of_true_literal _ c (.neg b.val) hlb
        exact fun h => hb ((basisValuation_at M U b).mp h)
    · apply satisfies_of_true_literal _ c (.neg a.val) hla
      exact fun h => ha ((basisValuation_at M U a).mp h)
  | newPoint =>
    obtain ⟨A,hA,heA⟩ := M.loopless e he
    obtain ⟨i,rfl⟩ := hcomplete A hA
    apply satisfies_of_true_literal _ c (.pos i.val) (hvalid i heA)
    exact fun h => h ((basisValuation_at M U i).mpr hA)
  | excluded w =>
    have hnot := hnone w
    unfold ModelMatch at hnot
    obtain ⟨j,hj⟩ := not_forall.mp hnot
    cases hbit : (models w).testBit j.val with
    | false =>
      have hm : U (newIndex j) ∈ M.bases := by
        by_contra hm
        apply hj
        simp [hm,hbit]
      apply satisfies_of_true_literal _ c (.pos (newIndex j).val)
        (by simpa [hbit] using hvalid j)
      exact fun h => h ((basisValuation_at M U (newIndex j)).mpr hm)
    | true =>
      have hm : U (newIndex j) ∉ M.bases := by
        intro hm
        apply hj
        simp [hm,hbit]
      apply satisfies_of_true_literal _ c (.neg (newIndex j).val)
        (by simpa [hbit] using hvalid j)
      exact fun h => hm ((basisValuation_at M U (newIndex j)).mp h)

/-- A complete semantic extension-cover theorem from an ordinary LRAT proof.
The candidate list is an output, not a hypothesis about the input family. -/
theorem exists_model_of_refutation {ground : Finset Point} {rank : ℕ}
    (M : BasisFamily ground rank) (U : Fin k → Finset Point) (e : Point)
    (old : Finset (Finset Point)) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (certificates : List (Origin k l × List Sat.Literal))
    (hcomplete : ∀ A ∈ M.bases, ∃ i : Fin k, U i = A)
    (he : e ∈ ground)
    (hold : ∀ i : Fin k, e ∉ U i → (U i ∈ M.bases ↔ U i ∈ old))
    (hvalid : ∀ oc ∈ certificates,
      ValidOrigin U e old newIndex models oc.1 oc.2)
    (hrefute : Sat.Fmla.proof (certificates.map Prod.snd) []) :
    ∃ w : Fin l, ModelMatch M U newIndex (models w) := by
  classical
  by_contra h
  have hnone : ∀ w, ¬ModelMatch M U newIndex (models w) := by
    intro w hw
    exact h ⟨w,hw⟩
  apply hrefute (basisValuation M U)
  constructor
  intro c hc
  obtain ⟨oc,hoc,rfl⟩ := List.mem_map.mp hc
  exact origin_sound M U e old newIndex models hcomplete he hold hnone
    oc.1 oc.2 (hvalid oc hoc)

end Papers.RationalityTen.BasisExtensionCNF
