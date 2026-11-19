module

public import PaperVerification.OrthogonalLatticeProjection
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

/-!
# Existence of the finite glue data for rational orthogonal subspaces

Rationality means that the lattice intersection spans the real subspace.
The sum of the two intersections is consequently a full lattice.  Its index
in the original lattice is finite, by the full-rank finite-quotient theorem
for finite free integer modules.  Coset representatives of this quotient
provide exactly the glue data in Proposition 6.1.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A subspace rational for a lattice is spanned by its lattice intersection. -/
def LatticeRational (L : Submodule ℤ E) (H : Submodule ℝ E) : Prop :=
  Submodule.span ℝ ((L ⊓ H.restrictScalars ℤ : Submodule ℤ E) : Set E) = H

def orthogonalGlueSubmodule (L : Submodule ℤ E) (H : Submodule ℝ E) : Submodule ℤ E :=
  (L ⊓ H.restrictScalars ℤ) ⊔ (L ⊓ Hᗮ.restrictScalars ℤ)

theorem orthogonalGlueSubmodule_le (L : Submodule ℤ E) (H : Submodule ℝ E) :
    orthogonalGlueSubmodule L H ≤ L :=
  sup_le inf_le_left inf_le_left

def orthogonalGlueRelation (L : Submodule ℤ E) (H : Submodule ℝ E) : Submodule ℤ L :=
  (orthogonalGlueSubmodule L H).comap L.subtype

abbrev OrthogonalGlueQuotient (L : Submodule ℤ E) (H : Submodule ℝ E) :=
  L ⧸ orthogonalGlueRelation L H

def glueRepresentative (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) : L := Quotient.out g

def glueProjectedRepresentative (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) : H :=
  ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm
    (glueRepresentative L H g : E)).1

def glueFibreRepresentative (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) : Hᗮ :=
  ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm
    (glueRepresentative L H g : E)).2

theorem glueRepresentative_decomposition (L : Submodule ℤ E) (H : Submodule ℝ E)
    (g : OrthogonalGlueQuotient L H) :
    (glueProjectedRepresentative L H g : E) + (glueFibreRepresentative L H g : E) =
      (glueRepresentative L H g : E) :=
  (H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).apply_symm_apply _

/-- Canonical quotient representatives give the literal glue decomposition.
This construction does not require finiteness of the quotient. -/
theorem canonical_orthogonal_glue (L : Submodule ℤ E) (H : Submodule ℝ E) :
    HasOrthogonalGlue L H (glueProjectedRepresentative L H) (glueFibreRepresentative L H) := by
  intro z
  constructor
  · intro hz
    let zL : L := ⟨z, hz⟩
    let g : OrthogonalGlueQuotient L H := Submodule.Quotient.mk zL
    have heq : (Submodule.Quotient.mk zL : OrthogonalGlueQuotient L H) =
        Submodule.Quotient.mk (glueRepresentative L H g) := by
      rw [glueRepresentative, Submodule.Quotient.mk_out]
    have hdiff := (Submodule.Quotient.eq (orthogonalGlueRelation L H)).mp heq
    change z - (glueRepresentative L H g : E) ∈ orthogonalGlueSubmodule L H at hdiff
    obtain ⟨n, hn, f, hf, hnf⟩ := Submodule.mem_sup.mp hdiff
    let nH : H := ⟨n, hn.2⟩
    let fW : Hᗮ := ⟨f, hf.2⟩
    refine ⟨g, nH + glueProjectedRepresentative L H g,
      fW + glueFibreRepresentative L H g, ?_, ?_, ?_⟩
    · change ((nH + glueProjectedRepresentative L H g) -
        glueProjectedRepresentative L H g : H) ∈ latticeIntersection L H
      rw [add_sub_cancel_right]
      change n ∈ L
      exact hn.1
    · change ((fW + glueFibreRepresentative L H g) -
        glueFibreRepresentative L H g : Hᗮ) ∈ latticeIntersection L Hᗮ
      rw [add_sub_cancel_right]
      change f ∈ L
      exact hf.1
    · have hrep := glueRepresentative_decomposition L H g
      simp only [Submodule.coe_add]
      change z = (n + (glueProjectedRepresentative L H g : E)) +
        (f + (glueFibreRepresentative L H g : E))
      have hzsum : z = (n + f) + (glueRepresentative L H g : E) :=
        sub_eq_iff_eq_add.mp hnf.symm
      rw [hzsum]
      rw [← hrep]
      abel
  · rintro ⟨g, x, t, hx, ht, rfl⟩
    have hxL : ((x : E) - (glueProjectedRepresentative L H g : E)) ∈ L := hx
    have htL : ((t : E) - (glueFibreRepresentative L H g : E)) ∈ L := ht
    have hrep := (glueRepresentative L H g).property
    have hsum := L.add_mem (L.add_mem hxL htL) hrep
    convert hsum using 1
    rw [← glueRepresentative_decomposition L H g]
    abel

/-- The canonical projected cosets are distinct.  Equality of the projected
cosets forces equality in the quotient by the two actual intersections. -/
theorem canonical_projected_cosets_distinct (L : Submodule ℤ E) (H : Submodule ℝ E) :
    Pairwise (fun g g' : OrthogonalGlueQuotient L H =>
      glueProjectedRepresentative L H g - glueProjectedRepresentative L H g' ∉
        latticeIntersection L H) := by
  intro g g' hne hproj
  apply hne
  have hprojL : ((glueProjectedRepresentative L H g : E) -
      (glueProjectedRepresentative L H g' : E)) ∈ L := hproj
  have hdiffL := L.sub_mem (glueRepresentative L H g).property
    (glueRepresentative L H g').property
  have hfibreL : ((glueFibreRepresentative L H g : E) -
      (glueFibreRepresentative L H g' : E)) ∈ L := by
    have hm := L.sub_mem hdiffL hprojL
    convert hm using 1
    rw [← glueRepresentative_decomposition L H g,
      ← glueRepresentative_decomposition L H g']
    abel
  have hsum : (glueRepresentative L H g : E) - (glueRepresentative L H g' : E) ∈
      orthogonalGlueSubmodule L H := by
    have hm := Submodule.add_mem_sup
      (show ((glueProjectedRepresentative L H g : E) -
        (glueProjectedRepresentative L H g' : E)) ∈ L ⊓ H.restrictScalars ℤ from
        ⟨hprojL, H.sub_mem (glueProjectedRepresentative L H g).property
          (glueProjectedRepresentative L H g').property⟩)
      (show ((glueFibreRepresentative L H g : E) -
        (glueFibreRepresentative L H g' : E)) ∈ L ⊓ Hᗮ.restrictScalars ℤ from
        ⟨hfibreL, Hᗮ.sub_mem (glueFibreRepresentative L H g).property
          (glueFibreRepresentative L H g').property⟩)
    change (glueRepresentative L H g : E) - (glueRepresentative L H g' : E) ∈
      (L ⊓ H.restrictScalars ℤ) ⊔ (L ⊓ Hᗮ.restrictScalars ℤ)
    convert hm using 1
    rw [← glueRepresentative_decomposition L H g,
      ← glueRepresentative_decomposition L H g']
    abel
  have hq := (Submodule.Quotient.eq (orthogonalGlueRelation L H)).mpr
    (show glueRepresentative L H g - glueRepresentative L H g' ∈
      orthogonalGlueRelation L H from hsum)
  simpa only [glueRepresentative, Submodule.Quotient.mk_out] using hq

/-- Rational complementary subspaces give a full-rank sum of intersections. -/
theorem orthogonalGlueSubmodule_span_top (L : Submodule ℤ E) (H : Submodule ℝ E)
    (hH : LatticeRational L H) (hW : LatticeRational L Hᗮ) :
    Submodule.span ℝ (orthogonalGlueSubmodule L H : Set E) = ⊤ := by
  apply le_antisymm le_top
  rw [← H.isCompl_orthogonal.sup_eq_top]
  apply sup_le
  · calc
      H = Submodule.span ℝ ((L ⊓ H.restrictScalars ℤ : Submodule ℤ E) : Set E) := hH.symm
      _ ≤ Submodule.span ℝ (orthogonalGlueSubmodule L H : Set E) :=
        Submodule.span_mono (fun _ hx => Submodule.mem_sup_left hx)
  · calc
      Hᗮ = Submodule.span ℝ ((L ⊓ Hᗮ.restrictScalars ℤ : Submodule ℤ E) : Set E) := hW.symm
      _ ≤ Submodule.span ℝ (orthogonalGlueSubmodule L H : Set E) :=
        Submodule.span_mono (fun _ hx => Submodule.mem_sup_right hx)

/-- The finite glue assertion follows from rationality; it is not an extra
finite-index assumption on the lattice or the subspaces. -/
theorem finite_orthogonalGlueQuotient
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (H : Submodule ℝ E) (hH : LatticeRational L H) (hW : LatticeRational L Hᗮ) :
    Finite (OrthogonalGlueQuotient L H) := by
  let K := orthogonalGlueSubmodule L H
  have hKL : K ≤ L := orthogonalGlueSubmodule_le L H
  letI : DiscreteTopology K := DiscreteTopology.of_subset
    (inferInstanceAs (DiscreteTopology L)) hKL
  letI : IsZLattice ℝ K := ⟨orthogonalGlueSubmodule_span_top L H hH hW⟩
  have hrank : Module.finrank ℤ (orthogonalGlueRelation L H) = Module.finrank ℤ L := by
    calc
      Module.finrank ℤ (orthogonalGlueRelation L H) = Module.finrank ℤ K :=
        (Submodule.comapSubtypeEquivOfLe hKL).finrank_eq
      _ = Module.finrank ℝ E := ZLattice.rank ℝ K
      _ = Module.finrank ℤ L := (ZLattice.rank ℝ L).symm
  exact Submodule.finiteQuotientOfFreeOfRankEq (orthogonalGlueRelation L H) hrank

/-- The full rational-subspace form of Proposition 6.1.  All finite glue data
are now constructed from the original lattice and subspace. -/
theorem rational_orthogonal_lattice_projection_transfer
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (H : Submodule ℝ E) (hH : LatticeRational L H) (hW : LatticeRational L Hᗮ)
    (t₀ : Hᗮ) (c : ℝ → ℝ)
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g : OrthogonalGlueQuotient L H,
      normSetGaussian (latticeCoset (latticeIntersection L Hᗮ)
        (glueFibreRepresentative L H g)) α t₀ = c α)
    (K : Set E)
    (hK : ∀ α : ℝ, 0 < α → ∀ z : E,
      NormColdSpot (L : Set E) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : H, (x₀ : E) + (t₀ : E) ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : H,
      NormColdSpot (latticeOrthogonalProjection L H : Set H) α x ↔
        (x : E) + (t₀ : E) ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (normSetGaussian (latticeOrthogonalProjection L H : Set H) α)) =
        sInf (Set.range (normSetGaussian (L : Set E) α)) / c α) ∧
    ((∀ z : E, z ∈ K ↔ NormDeepHole (L : Set E) z) → ∀ x : H,
      NormDeepHole (latticeOrthogonalProjection L H : Set H) x ↔
        (x : E) + (t₀ : E) ∈ K) := by
  letI : Finite (OrthogonalGlueQuotient L H) := finite_orthogonalGlueQuotient L H hH hW
  letI : Fintype (OrthogonalGlueQuotient L H) := Fintype.ofFinite _
  exact orthogonal_lattice_projection_transfer L H
    (glueProjectedRepresentative L H) (glueFibreRepresentative L H)
    (canonical_orthogonal_glue L H) (canonical_projected_cosets_distinct L H)
    t₀ c hfibre K hK hmeet

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.finite_orthogonalGlueQuotient
#print axioms PaperVerification.ColdSpots.rational_orthogonal_lattice_projection_transfer
