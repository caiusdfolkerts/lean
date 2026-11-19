module

public import ToricPower.SimplicialPrimitiveBasis
public import ToricPower.CompleteFanMaximalDimension

/-!
# Full-dimensional cones in a simplicial stellar subdivision

A full-dimensional new cone is the cone on a facet of an original
full-dimensional simplicial cone. In its actual primitive-ray basis,
this replaces exactly one ray by the new point, and the replaced
coordinate is strictly positive. These are the geometric hypotheses
of the determinant decrease argument.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {C F : PointedCone ℝ V} {p : V}

theorem span_rayJoin (p : V) (F : PointedCone ℝ V) :
    Submodule.span ℝ (rayJoin p F : Set V) =
      Submodule.span ℝ (F : Set V) ⊔ Submodule.span ℝ ({p} : Set V) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := mem_rayJoin.mp hx
    apply (Submodule.span ℝ (F : Set V) ⊔ Submodule.span ℝ ({p} : Set V)).add_mem
    · exact Submodule.mem_sup_right
        (Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton p)))
    · exact Submodule.mem_sup_left (Submodule.subset_span hy)
  · apply sup_le
    · exact Submodule.span_mono (le_rayJoin p F)
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
        (Submodule.subset_span (point_mem_rayJoin p F)))

theorem coneDimension_rayJoin [FiniteDimensional ℝ V]
    (outside : p ∉ Submodule.span ℝ (F : Set V)) :
    coneDimension (rayJoin p F) = coneDimension F + 1 := by
  dsimp [coneDimension]
  rw [span_rayJoin]
  exact Submodule.finrank_sup_span_singleton outside

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem range_update_basis (basis : Module.Basis κ ℝ V) (j : κ) (p : V) :
    Set.range (Function.update (basis : κ → V) j p) =
      ({p} : Set V) ∪ basis '' ({j}ᶜ : Set κ) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    by_cases equal : k = j
    · subst k
      exact Or.inl (by simp)
    · exact Or.inr ⟨k, by simpa using equal, by simp [equal]⟩
  · rintro (h | ⟨k, hk, rfl⟩)
    · refine ⟨j, ?_⟩
      simpa using h.symm
    · have different : k ≠ j := by simpa using hk
      exact ⟨k, Function.update_of_ne different _ _⟩

/-- A full-dimensional cone on a proper face of a basis cone replaces
exactly one vector of that basis. -/
theorem fullDimensional_rayJoin_eq_update (basis : Module.Basis κ ℝ V)
    (basisCone : C = PointedCone.hull ℝ (Set.range basis))
    (face : F.IsFaceOf C) (point : p ∈ C) (outside : p ∉ F)
    (full : Submodule.span ℝ (rayJoin p F : Set V) = ⊤) :
    ∃ j : κ, 0 < basis.repr p j ∧
      F = PointedCone.hull ℝ (basis '' ({j}ᶜ : Set κ)) ∧
      rayJoin p F = PointedCone.hull ℝ (Set.range (Function.update (basis : κ → V) j p)) := by
  letI := Module.Finite.of_basis basis
  let A : Set κ := {k | basis k ∈ F}
  have faceSpans : F = PointedCone.hull ℝ (basis '' A) :=
    PointedCone.Face.eq_hull_image ⟨F, face⟩ basisCone
  have faceDimension : coneDimension F = A.ncard := by
    have h := TauCeti.finrank_span_face_eq_card_faceOrderIsoSet
      (basis : κ → V) basis.linearIndependent basisCone (⟨F, face⟩ : C.Face)
    simpa only [coneDimension, PointedCone.faceOrderIsoSet_apply,
      ← PointedCone.Face.mem_toPointedCone, PointedCone.Face.toPointedCone,
      Nat.card_coe_set_eq] using h
  have dimension : Nat.card κ = 1 + A.ncard := by
    have h := coneDimension_rayJoin (point_not_mem_span_face face point outside)
    dsimp [coneDimension] at h
    rw [full, finrank_top, Module.finrank_eq_nat_card_basis basis] at h
    change Nat.card κ = coneDimension F + 1 at h
    rw [faceDimension] at h
    omega
  obtain ⟨j, complement⟩ := Set.ncard_eq_one.mp (Set.ncard_compl_of_ncard_eq_add A dimension)
  have Aeq : A = ({j}ᶜ : Set κ) := by
    rw [← compl_compl A, complement]
  have facet : F = PointedCone.hull ℝ (basis '' ({j}ᶜ : Set κ)) := faceSpans.trans (by rw [Aeq])
  have coordinates : ∀ k, 0 ≤ basis.repr p k := by
    have hp : p ∈ PointedCone.hull ℝ (basis '' (Set.univ : Set κ)) := by
      rw [Set.image_univ, ← basisCone]
      exact point
    exact ((mem_basisCone_iff basis Set.univ p).mp hp).1
  have positive : 0 < basis.repr p j := by
    apply lt_of_le_of_ne (coordinates j)
    intro zero
    apply outside
    rw [facet]
    apply (mem_basisCone_iff basis ({j}ᶜ : Set κ) p).mpr
    refine ⟨coordinates, ?_⟩
    intro k hk
    have equal : k = j := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hk
    simpa only [equal] using zero.symm
  refine ⟨j, positive, facet, ?_⟩
  rw [range_update_basis]
  change PointedCone.hull ℝ {p} ⊔ F = _
  rw [facet]
  exact (Submodule.span_union _ _).symm

variable {N : Type*} [AddCommGroup N] {i : N →+ V}

/-- Every full-dimensional new stellar cone is obtained by the literal
one-column replacement in a full-dimensional old cone. -/
theorem stellarFan_fullDimensional_cases (fan : Fan i) (complete : fan.IsComplete)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (q : N)
    {S : PointedCone ℝ V} (member : S ∈ (stellarFan fan q).cones)
    (full : Submodule.span ℝ (S : Set V) = ⊤) :
    (S ∈ fan.cones ∧ i q ∉ S) ∨
      ∃ (C : PointedCone ℝ V) (hC : C ∈ fan.cones)
        (fullC : Submodule.span ℝ (C : Set V) = ⊤),
        i q ∈ C ∧ ∃ j : ToricRay C,
          0 < (simplicialPrimitiveBasis fan.lattice (fan.isToricCone hC)
            (simplicial C hC) fullC).repr (i q) j ∧
          S = PointedCone.hull ℝ (Set.range (Function.update
            (simplicialPrimitiveBasis fan.lattice (fan.isToricCone hC)
              (simplicial C hC) fullC : ToricRay C → V) j (i q))) := by
  rcases (stellarFan_mem_iff fan q).mp member with old |
    ⟨τ, ⟨hτ, hpτ, σ, hσ, hpσ, hτσ⟩, rfl⟩
  · exact Or.inl old
  · right
    obtain ⟨C, hC, σFace, fullC⟩ := exists_fullDimensional_supercone fan complete hσ
    letI := ToricRay.finite_of_fg (fan.isToricCone hC).fg
    letI := Fintype.ofFinite (ToricRay C)
    let basis := simplicialPrimitiveBasis fan.lattice (fan.isToricCone hC) (simplicial C hC) fullC
    obtain ⟨j, positive, _, cone⟩ := fullDimensional_rayJoin_eq_update basis
      (simplicialPrimitiveBasis_hull fan.lattice (fan.isToricCone hC) (simplicial C hC) fullC).symm
      ((fan.isFaceOf_of_le hσ hτ hτσ).trans σFace) (σFace.le hpσ) hpτ full
    exact ⟨C, hC, fullC, σFace.le hpσ, j, positive, cone⟩

end ToricPower.FanSubdivision
end
