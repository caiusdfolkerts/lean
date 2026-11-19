module

public import ToricPower.DiagonalGlobalColumns
public import ToricPower.DiagonalChartExactness

/-!
# The global cellular matrix restricts to the actual strip complex

The inclusion of a literal weight strip into the universal cover is an
actual cellular map which keeps each characteristic disk unchanged.
Consequently its entire boundary column is the restriction of the actual
ambient boundary, including zero coefficients outside the strip.

Lattice translation then identifies the coefficient of each global
monomial entry with the coefficient of the already constructed local
weight complex.  This is a geometric comparison of two independently
defined matrices, not an exactness convention for the global matrix.

Candidate until its complete dependency closure has passed Lean.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local instance diagonalStripComparisonPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

local instance diagonalStripComparisonStripCW (S T : Set (Fin s)) (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

/-- The literal topological inclusion of a weight strip. -/
def diagonalStripInclusion (S T : Set (Fin s)) (u : Fin n → ℤ) :
    TopCat.of (diagonalStripCarrier A S T u) ⟶
      TopCat.of (arrangementCarrier A) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, Set.mem_univ _⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem diagonalStripInclusion_cellular (S T : Set (Fin s)) (u : Fin n → ℤ) :
    TauCeti.IsCellular (diagonalStripCarrier A S T u)
      (arrangementCarrier A) (diagonalStripInclusion A S T u) := by
  intro m x hx
  obtain ⟨d, hd, c, hc⟩ := CWComplex.mem_skeletonLT_iff.mp hx
  apply CWComplex.mem_skeletonLT_iff.mpr
  exact ⟨d, hd, c.val, hc⟩

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion preserves the actual characteristic map, with its
disk parameter and orientation, on each cell. -/
theorem diagonalStripInclusion_characteristic (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ) (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d) :
    TauCeti.characteristicCellPairMap (diagonalStripCarrier A S T u) c ≫
      TauCeti.skeletonPairMap _ _ (diagonalStripInclusion_cellular A S T u) d =
        TauCeti.characteristicCellPairMap (arrangementCarrier A) c.val := by
  apply TopPair.hom_ext_of_fst
  rw [TopPair.Hom.fst_comp, TauCeti.skeletonPairMap_fst]
  ext x
  erw [ConcreteCategory.comp_apply]
  apply Subtype.ext
  let y : TauCeti.skeletonObj (diagonalStripCarrier A S T u) (d + 1) :=
    TopPair.Hom.fst (TauCeti.characteristicCellPairMap (diagonalStripCarrier A S T u) c) x
  let v := (EuclideanSpace.equiv (Fin d) ℝ).unitBallHomeomorph (x : TopCat.disk d).down
  have sourceValue : (y : Fin n → ℝ) = periodicCellMap A c.val v :=
    TauCeti.coe_characteristicCellPairMap_fst_apply (diagonalStripCarrier A S T u) c x
  have targetValue :
      ((TopPair.Hom.fst (TauCeti.characteristicCellPairMap
        (arrangementCarrier A) c.val)) x).val = periodicCellMap A c.val v :=
    TauCeti.coe_characteristicCellPairMap_fst_apply (arrangementCarrier A) c.val x
  have includedValue := congrArg Subtype.val
    (TauCeti.skeletonMap_apply (diagonalStripCarrier A S T u)
      (arrangementCarrier A) (diagonalStripInclusion_cellular A S T u) (d + 1) y)
  change _ = (y : Fin n → ℝ) at includedValue
  exact includedValue.trans (sourceValue.trans targetValue.symm)

variable (k : Type) [Ring k]

/-- Every ambient boundary coefficient of an allowed source is already
in the actual strip complex; this equality also records all outside
coefficients as zero. -/
theorem diagonalStrip_boundaryColumn_ambient (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ) (j : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) (d+1)) :
    TauCeti.cellularBoundaryColumn (arrangementCarrier A) k d j.val =
      Finsupp.mapDomain Subtype.val
        (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T u) k d j) :=
  cellularBoundaryColumn_naturality _ _ (diagonalStripInclusion_cellular A S T u) k
    (fun _ c => c.val) (diagonalStripInclusion_characteristic A S T u) d j

/-- Entrywise form of the actual strip-to-ambient comparison. -/
theorem diagonalStrip_incidence_ambient (S T : Set (Fin s))
    (u : Fin n → ℤ) (d : ℕ)
    (i : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) d)
    (j : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) (d+1)) :
    TauCeti.cellularIncidence (diagonalStripCarrier A S T u) k d i j =
      TauCeti.cellularIncidence (arrangementCarrier A) k d i.val j.val := by
  have h := congrArg (fun f => f i.val)
    (diagonalStrip_boundaryColumn_ambient A k S T u d j)
  rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective] at h
  exact (TauCeti.cellularBoundaryColumn_apply
    (diagonalStripCarrier A S T u) k d i j).symm.trans
    (h.symm.trans (TauCeti.cellularBoundaryColumn_apply
      (arrangementCarrier A) k d i.val j.val))

/-- Every supported global term sends a genuine source monomial to a
genuine target monomial on every pair of affine charts. -/
theorem diagonalGlobalTerm_monomialAllowed (S T : Set (Fin s))
    (u v : Fin n → ℤ) (d : ℕ) (j : NormalizedCell A (d+1))
    (hj : diagonalMonomialAllowed A S T u (j,v))
    (p : DiagonalGlobalColumnTerm k A d j) :
    diagonalMonomialAllowed A S T u (p.val.1,v+p.val.2) := by
  constructor
  · intro ρ hρ
    have hs := hj.1 ρ hρ
    have ht := (diagonalGlobalColumnTerm_regular k A d j p ρ).1
    change reflectedCeiling A j.val ρ ≤ rayPairing A v ρ at hs
    change reflectedCeiling A p.val.1.val ρ ≤ rayPairing A (v + p.val.2) ρ
    rw [rayPairing_add]
    omega
  · intro ρ hρ
    have hs := hj.2 ρ hρ
    have ht := (diagonalGlobalColumnTerm_regular k A d j p ρ).2
    change j.val.val.1 (.inl ρ) ≤ rayPairing A (u - v) ρ at hs
    change p.val.1.val.val.1 (.inl ρ) ≤ rayPairing A (u - (v + p.val.2)) ρ
    rw [rayPairing_sub, rayPairing_add]
    rw [rayPairing_sub] at hs
    omega

/-- The local coefficient attached to multiplying by `(a,-a)` is exactly
the global normalized-column coefficient.  The proof uses actual strip
inclusion and actual translation invariance of cellular local degrees. -/
theorem diagonalStrip_incidence_globalColumn (S T : Set (Fin s))
    (u v a : Fin n → ℤ) (d : ℕ)
    (i : NormalizedCell A d) (j : NormalizedCell A (d+1))
    (hi : stripCellAllowed A S T u (translateCell A (v+a) i.val))
    (hj : stripCellAllowed A S T u (translateCell A v j.val)) :
    TauCeti.cellularIncidence (diagonalStripCarrier A S T u) k d
        (⟨translateCell A (v+a) i.val, hi⟩ :
          Topology.RelCWComplex.cell (D := ∅) (diagonalStripCarrier A S T u) d)
        (⟨translateCell A v j.val, hj⟩ :
          Topology.RelCWComplex.cell (D := ∅) (diagonalStripCarrier A S T u) (d+1)) =
      diagonalGlobalColumn k A d j (i,a) := by
  refine (diagonalStrip_incidence_ambient A k S T u d
    (⟨translateCell A (v+a) i.val, hi⟩ :
      Topology.RelCWComplex.cell (D := ∅) (diagonalStripCarrier A S T u) d)
    (⟨translateCell A v j.val, hj⟩ :
      Topology.RelCWComplex.cell (D := ∅) (diagonalStripCarrier A S T u) (d+1))).trans ?_
  rw [diagonalGlobalColumn_apply]
  change TauCeti.cellularIncidence (arrangementCarrier A) k d
    (translateCell A (v+a) i.val) (translateCell A v j.val) =
    TauCeti.cellularIncidence (arrangementCarrier A) k d (translateCell A a i.val) j.val
  have htranslate : translateCell A (v+a) i.val =
      translateCell A v (translateCell A a i.val) := by
    rw [translateCell_add, add_comm]
  rw [htranslate]
  exact arrangement_cellularIncidence_translate A k v d (translateCell A a i.val) j.val

end ToricPower.IntegralArrangement
