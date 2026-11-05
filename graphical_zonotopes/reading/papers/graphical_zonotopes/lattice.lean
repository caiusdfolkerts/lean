module

public import Papers.GraphicalZonotopes.Zonotope

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integer-valued lower-support data in the fixed standard lattice. -/
def IntegerValued (z : SetFunction V) : Prop := ∀ S, ∃ a : ℤ, z S = (a : ℝ)

/-- Convex hull of finitely many standard integer coordinate vectors. -/
def LatticePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ P : Finset (V → ℤ), Q = convexHull ℝ ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ)))

def integerValue {z : SetFunction V} (hz : IntegerValued z) (S : Finset V) : ℤ :=
  Classical.choose (hz S)

@[simp] theorem cast_integerValue {z : SetFunction V} (hz : IntegerValued z) (S : Finset V) :
    (integerValue hz S : ℝ) = z S := (Classical.choose_spec (hz S)).symm

def integerGreedyPoint {z : SetFunction V} (hz : IntegerValued z)
    (e : Fin (Fintype.card V) ≃ V) (v : V) : ℤ :=
  integerValue hz (orderPrefix e ((e.symm v).val + 1)) -
    integerValue hz (orderPrefix e (e.symm v).val)

@[simp] theorem cast_integerGreedyPoint {z : SetFunction V} (hz : IntegerValued z)
    (e : Fin (Fintype.card V) ≃ V) :
    (fun v => (integerGreedyPoint hz e v : ℝ)) = greedyPoint z e := by
  funext v
  simp [integerGreedyPoint, greedyPoint]

theorem IntegerValued.basePolytope {z : SetFunction V} (hz : IntegerValued z)
    (hn : Normalized z) (hs : Supermodular z) : LatticePolytope (basePolytope z) := by
  classical
  let P : Finset (V → ℤ) := univ.image (integerGreedyPoint hz)
  refine ⟨P, ?_⟩
  rw [basePolytope_eq_convexHull hn hs]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨integerGreedyPoint hz e, ?_, cast_integerGreedyPoint hz e⟩
    simp [P]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨e, he, rfl⟩ := mem_image.mp hy
    exact ⟨e, (cast_integerGreedyPoint hz e).symm⟩

theorem IntegerValued.add {z w : SetFunction V} (hz : IntegerValued z)
    (hw : IntegerValued w) : IntegerValued (z + w) := by
  intro S
  obtain ⟨a, ha⟩ := hz S
  obtain ⟨b, hb⟩ := hw S
  exact ⟨a + b, by simp [ha, hb]⟩

theorem IntegerValued.sub {z w : SetFunction V} (hz : IntegerValued z)
    (hw : IntegerValued w) : IntegerValued (z - w) := by
  intro S
  obtain ⟨a, ha⟩ := hz S
  obtain ⟨b, hb⟩ := hw S
  exact ⟨a - b, by simp [ha, hb]⟩

theorem IntegerValued.int_smul {z : SetFunction V} (hz : IntegerValued z)
    (m : ℤ) : IntegerValued ((m : ℝ) • z) := by
  intro S
  obtain ⟨a, ha⟩ := hz S
  exact ⟨m * a, by simp [ha]⟩

theorem IntegerValued.finset_sum {I : Type*} (t : Finset I) (f : I → SetFunction V)
    (hf : ∀ i ∈ t, IntegerValued (f i)) : IntegerValued (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro S; exact ⟨0, by simp⟩
  | @insert i t hi ih =>
    rw [sum_insert hi]
    exact (hf i (mem_insert_self _ _)).add (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem setMonomial_integerValued (C : Finset V) : IntegerValued (setMonomial C) := by
  intro S
  by_cases h : C ⊆ S
  · exact ⟨1, by simp [setMonomial, h]⟩
  · exact ⟨0, by simp [setMonomial, h]⟩

theorem zeta_integerValued {y : SetFunction V} (hy : IntegerValued y) :
    IntegerValued (zeta y) := by
  intro S
  refine ⟨∑ C ∈ S.powerset, integerValue hy C, ?_⟩
  simp [zeta]

theorem graphFunction_integerValued (G : SimpleGraph V) : IntegerValued (graphFunction G) :=
  IntegerValued.finset_sum _ _ (fun C hC => setMonomial_integerValued C)

end GraphicalZonotopes
