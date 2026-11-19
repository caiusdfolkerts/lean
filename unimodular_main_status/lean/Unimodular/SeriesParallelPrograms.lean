module

public import Unimodular.RankThreeGeometry

@[expose] public section

/-!
# Constructive series--parallel programs and exact represented minors

Programs use singleton direct summands and the literal parallel and series
extensions of represented matroids. Admissibility records the usual eligibility
conditions. The minor witness records the contracted original rays and the
kernel of an actual linear map; the quotient independence theorem below is its
semantic connection to vector-matroid contraction and deletion.
-/

namespace Unimodular.SeriesParallel

open scoped BigOperators

/-- A finite construction by singleton summands and series/parallel extensions.
The index is the exact number of represented elements. -/
inductive SPProgram : ℕ → Type
  | empty : SPProgram 0
  | addLoop {m : ℕ} (P : SPProgram m) : SPProgram (m + 1)
  | addColoop {m : ℕ} (P : SPProgram m) : SPProgram (m + 1)
  | parallel {m : ℕ} (P : SPProgram m) (e : Fin m) : SPProgram (m + 1)
  | series {m : ℕ} (P : SPProgram m) (e : Fin m) : SPProgram (m + 1)
  | relabel {m : ℕ} (P : SPProgram m) (e : Equiv.Perm (Fin m)) : SPProgram m

/-- Add a zero first coordinate. -/
def liftColumn {m : ℕ} (u : Lattice m) : Lattice (m + 1) := Fin.cons 0 u

/-- The independent new coordinate. -/
def newColumn (m : ℕ) : Lattice (m + 1) := Fin.cons 1 0

namespace SPProgram

/-- Literal integral columns for the construction. A series step replaces the
selected old column by `(1,u)` and adjoins `(-1,0)`; the two new columns sum to
the lifted old column. -/
def columns : {m : ℕ} → SPProgram m → Fin m → Lattice m
  | _, .empty => Fin.elim0
  | _, .addLoop P => Fin.cons 0 (fun j => liftColumn (columns P j))
  | m + 1, .addColoop P => Fin.cons (newColumn m) (fun j => liftColumn (columns P j))
  | _, .parallel P e =>
      Fin.cons (liftColumn (columns P e)) (fun j => liftColumn (columns P j))
  | _, .series P e =>
      Fin.cons (Fin.cons (-1) 0)
        (fun j => if j = e then Fin.cons 1 (columns P e) else liftColumn (columns P j))
  | _, .relabel P e => columns P ∘ e

/-- Eligibility is the ordinary nonloop condition for a parallel extension and
the ordinary noncoloop condition for a series extension. Singleton summands
allow all disconnected series--parallel matroids. -/
def Admissible : {m : ℕ} → SPProgram m → Prop
  | _, .empty => True
  | _, .addLoop P => P.Admissible
  | _, .addColoop P => P.Admissible
  | _, .parallel P e => P.Admissible ∧ P.columns e ≠ 0
  | _, .series P e => P.Admissible ∧
      embed (P.columns e) ∈ Submodule.span ℝ
        {v | ∃ j, j ≠ e ∧ embed (P.columns j) = v}
  | _, .relabel P _ => P.Admissible

@[simp] theorem columns_relabel {m : ℕ} (P : SPProgram m)
    (e : Equiv.Perm (Fin m)) (j : Fin m) : (P.relabel e).columns j = P.columns (e j) := rfl

@[simp] theorem columns_addLoop_zero {m : ℕ} (P : SPProgram m) :
    P.addLoop.columns 0 = 0 := rfl

@[simp] theorem columns_addLoop_succ {m : ℕ} (P : SPProgram m) (j : Fin m) :
    P.addLoop.columns j.succ = liftColumn (P.columns j) := rfl

@[simp] theorem columns_addColoop_zero {m : ℕ} (P : SPProgram m) :
    P.addColoop.columns 0 = newColumn m := rfl

@[simp] theorem columns_addColoop_succ {m : ℕ} (P : SPProgram m) (j : Fin m) :
    P.addColoop.columns j.succ = liftColumn (P.columns j) := rfl

@[simp] theorem columns_parallel_zero {m : ℕ} (P : SPProgram m) (e : Fin m) :
    (P.parallel e).columns 0 = liftColumn (P.columns e) := rfl

@[simp] theorem columns_parallel_succ {m : ℕ} (P : SPProgram m) (e j : Fin m) :
    (P.parallel e).columns j.succ = liftColumn (P.columns j) := rfl

@[simp] theorem columns_series_zero {m : ℕ} (P : SPProgram m) (e : Fin m) :
    (P.series e).columns 0 = Fin.cons (-1) 0 := rfl

@[simp] theorem columns_series_selected {m : ℕ} (P : SPProgram m) (e : Fin m) :
    (P.series e).columns e.succ = Fin.cons 1 (P.columns e) := by
  simp [columns]

@[simp] theorem columns_series_other {m : ℕ} (P : SPProgram m) (e j : Fin m)
    (hje : j ≠ e) :
    (P.series e).columns j.succ = liftColumn (P.columns j) := by
  simp [columns, hje]

end SPProgram

/-- Equality of all independent subsets, the literal represented-matroid
meaning, rather than equality only of rank or of maximal determinants. -/
def SameIndependence {E : Type*} {d d' : ℕ} (U : E → Lattice d)
    (W : E → Lattice d') : Prop :=
  ∀ S : Set E,
    LinearIndependent ℝ (fun j : S => embed (U j.val)) ↔
      LinearIndependent ℝ (fun j : S => embed (W j.val))

/-- The constructive series--parallel class, with arbitrary relabeling of the
finite ground set allowed. -/
def IsSeriesParallelConfiguration {m d : ℕ} (U : Fin m → Lattice d) : Prop :=
  ∃ P : SPProgram m, P.Admissible ∧
    ∃ e : Equiv.Perm (Fin m), SameIndependence U (P.columns ∘ e)

/-- A genuine contraction-and-deletion witness inside the primitive rays of a
fan. The target space may have unused coordinates; exactness of the kernel is
what identifies the contraction lattice over the reals. -/
structure MinorWitness {m d n : ℕ} (fan : SmoothCompleteFan n)
    (U : Fin m → Lattice d) where
  chosen : Fin m ↪ Lattice n
  chosen_rays : ∀ j, chosen j ∈ fan.rays
  contracted : Finset (Lattice n)
  contracted_rays : ∀ u ∈ contracted, u ∈ fan.rays
  disjoint : ∀ j, chosen j ∉ contracted
  projection : Ambient n →ₗ[ℝ] Ambient d
  kernel : LinearMap.ker projection =
    Submodule.span ℝ (embed '' (contracted : Set (Lattice n)))
  image : ∀ j, projection (embed (chosen j)) = embed (U j)

namespace MinorWitness

noncomputable section

variable {m d n : ℕ} {fan : SmoothCompleteFan n} {U : Fin m → Lattice d}
  (h : MinorWitness fan U)

abbrev contractedSpan : Submodule ℝ (Ambient n) :=
  Submodule.span ℝ (embed '' (h.contracted : Set (Lattice n)))

/-- The actual quotient map induced by the witness, not an assumed equivalence
of represented matroids. -/
def quotientMap : (Ambient n ⧸ h.contractedSpan) →ₗ[ℝ] Ambient d :=
  h.contractedSpan.liftQ h.projection (by rw [h.kernel])

@[simp] theorem quotientMap_mk (x : Ambient n) :
    h.quotientMap (Submodule.Quotient.mk x) = h.projection x := rfl

lemma quotientMap_injective : Function.Injective h.quotientMap := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have hpx : h.projection x = 0 := hx
      have hmem : x ∈ h.contractedSpan := by
        dsimp only [contractedSpan]
        rw [← h.kernel]
        exact hpx
      simpa only [Submodule.mem_bot] using (Submodule.Quotient.mk_eq_zero h.contractedSpan).mpr hmem
  · exact bot_le

/-- Every subset has precisely the independent-set predicate of the selected
original rays after quotienting by the contracted rays. This proves the
semantic contraction-and-deletion claim carried by `MinorWitness`. -/
theorem independent_iff_quotient (S : Set (Fin m)) :
    LinearIndependent ℝ (fun j : S => embed (U j.val)) ↔
      LinearIndependent ℝ (fun j : S =>
        (Submodule.Quotient.mk (embed (h.chosen j.val)) : Ambient n ⧸ h.contractedSpan)) := by
  have he : (fun j : S => embed (U j.val)) = h.quotientMap ∘
      (fun j : S => (Submodule.Quotient.mk (embed (h.chosen j.val)) :
        Ambient n ⧸ h.contractedSpan)) := by
    funext j
    exact (h.image j.val).symm
  rw [he]
  exact h.quotientMap.linearIndependent_iff (LinearMap.ker_eq_bot.mpr h.quotientMap_injective)

end
end MinorWitness

#print axioms Unimodular.SeriesParallel.MinorWitness.independent_iff_quotient

end Unimodular.SeriesParallel
