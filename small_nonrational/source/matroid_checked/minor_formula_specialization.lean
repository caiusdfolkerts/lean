module
public import MatroidChecked.ChartPolynomial

@[expose] public section
/-! The70 literal formula specializations are generic over every commutative ring.
Each is proved by kernel reduction of the existing formula table, once. -/
namespace Papers.RationalityTen.MatroidChecked.ChartPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem minorFormula_at_0 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (0 : Fin 70) =
      1 := by rfl

theorem minorFormula_at_1 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (1 : Fin 70) =
      D 3 0 := by rfl

theorem minorFormula_at_2 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (2 : Fin 70) =
      D 3 1 := by rfl

theorem minorFormula_at_3 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (3 : Fin 70) =
      D 3 2 := by rfl

theorem minorFormula_at_4 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (4 : Fin 70) =
      D 3 3 := by rfl

theorem minorFormula_at_5 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (5 : Fin 70) =
      -D 2 0 := by rfl

theorem minorFormula_at_6 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (6 : Fin 70) =
      -D 2 1 := by rfl

theorem minorFormula_at_7 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (7 : Fin 70) =
      -D 2 2 := by rfl

theorem minorFormula_at_8 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (8 : Fin 70) =
      -D 2 3 := by rfl

theorem minorFormula_at_9 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (9 : Fin 70) =
      D 2 0 * D 3 1 - D 3 0 * D 2 1 := by rfl

theorem minorFormula_at_10 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (10 : Fin 70) =
      D 2 0 * D 3 2 - D 3 0 * D 2 2 := by rfl

theorem minorFormula_at_11 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (11 : Fin 70) =
      D 2 0 * D 3 3 - D 3 0 * D 2 3 := by rfl

theorem minorFormula_at_12 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (12 : Fin 70) =
      D 2 1 * D 3 2 - D 3 1 * D 2 2 := by rfl

theorem minorFormula_at_13 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (13 : Fin 70) =
      D 2 1 * D 3 3 - D 3 1 * D 2 3 := by rfl

theorem minorFormula_at_14 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (14 : Fin 70) =
      D 2 2 * D 3 3 - D 3 2 * D 2 3 := by rfl

theorem minorFormula_at_15 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (15 : Fin 70) =
      D 1 0 := by rfl

theorem minorFormula_at_16 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (16 : Fin 70) =
      D 1 1 := by rfl

theorem minorFormula_at_17 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (17 : Fin 70) =
      D 1 2 := by rfl

theorem minorFormula_at_18 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (18 : Fin 70) =
      D 1 3 := by rfl

theorem minorFormula_at_19 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (19 : Fin 70) =
      -D 1 0 * D 3 1 + D 3 0 * D 1 1 := by rfl

theorem minorFormula_at_20 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (20 : Fin 70) =
      -D 1 0 * D 3 2 + D 3 0 * D 1 2 := by rfl

theorem minorFormula_at_21 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (21 : Fin 70) =
      -D 1 0 * D 3 3 + D 3 0 * D 1 3 := by rfl

theorem minorFormula_at_22 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (22 : Fin 70) =
      -D 1 1 * D 3 2 + D 3 1 * D 1 2 := by rfl

theorem minorFormula_at_23 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (23 : Fin 70) =
      -D 1 1 * D 3 3 + D 3 1 * D 1 3 := by rfl

theorem minorFormula_at_24 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (24 : Fin 70) =
      -D 1 2 * D 3 3 + D 3 2 * D 1 3 := by rfl

theorem minorFormula_at_25 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (25 : Fin 70) =
      D 1 0 * D 2 1 - D 2 0 * D 1 1 := by rfl

theorem minorFormula_at_26 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (26 : Fin 70) =
      D 1 0 * D 2 2 - D 2 0 * D 1 2 := by rfl

theorem minorFormula_at_27 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (27 : Fin 70) =
      D 1 0 * D 2 3 - D 2 0 * D 1 3 := by rfl

theorem minorFormula_at_28 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (28 : Fin 70) =
      D 1 1 * D 2 2 - D 2 1 * D 1 2 := by rfl

theorem minorFormula_at_29 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (29 : Fin 70) =
      D 1 1 * D 2 3 - D 2 1 * D 1 3 := by rfl

theorem minorFormula_at_30 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (30 : Fin 70) =
      D 1 2 * D 2 3 - D 2 2 * D 1 3 := by rfl

theorem minorFormula_at_31 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (31 : Fin 70) =
      D 1 0 * D 2 1 * D 3 2 - D 1 0 * D 3 1 * D 2 2 - D 2 0 * D 1 1 * D 3 2 + D 2 0 * D 3 1 * D 1 2 + D 3 0 * D 1 1 * D 2 2 - D 3 0 * D 2 1 * D 1 2 := by rfl

theorem minorFormula_at_32 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (32 : Fin 70) =
      D 1 0 * D 2 1 * D 3 3 - D 1 0 * D 3 1 * D 2 3 - D 2 0 * D 1 1 * D 3 3 + D 2 0 * D 3 1 * D 1 3 + D 3 0 * D 1 1 * D 2 3 - D 3 0 * D 2 1 * D 1 3 := by rfl

theorem minorFormula_at_33 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (33 : Fin 70) =
      D 1 0 * D 2 2 * D 3 3 - D 1 0 * D 3 2 * D 2 3 - D 2 0 * D 1 2 * D 3 3 + D 2 0 * D 3 2 * D 1 3 + D 3 0 * D 1 2 * D 2 3 - D 3 0 * D 2 2 * D 1 3 := by rfl

theorem minorFormula_at_34 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (34 : Fin 70) =
      D 1 1 * D 2 2 * D 3 3 - D 1 1 * D 3 2 * D 2 3 - D 2 1 * D 1 2 * D 3 3 + D 2 1 * D 3 2 * D 1 3 + D 3 1 * D 1 2 * D 2 3 - D 3 1 * D 2 2 * D 1 3 := by rfl

theorem minorFormula_at_35 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (35 : Fin 70) =
      -D 0 0 := by rfl

theorem minorFormula_at_36 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (36 : Fin 70) =
      -D 0 1 := by rfl

theorem minorFormula_at_37 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (37 : Fin 70) =
      -D 0 2 := by rfl

theorem minorFormula_at_38 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (38 : Fin 70) =
      -D 0 3 := by rfl

theorem minorFormula_at_39 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (39 : Fin 70) =
      D 0 0 * D 3 1 - D 3 0 * D 0 1 := by rfl

theorem minorFormula_at_40 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (40 : Fin 70) =
      D 0 0 * D 3 2 - D 3 0 * D 0 2 := by rfl

theorem minorFormula_at_41 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (41 : Fin 70) =
      D 0 0 * D 3 3 - D 3 0 * D 0 3 := by rfl

theorem minorFormula_at_42 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (42 : Fin 70) =
      D 0 1 * D 3 2 - D 3 1 * D 0 2 := by rfl

theorem minorFormula_at_43 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (43 : Fin 70) =
      D 0 1 * D 3 3 - D 3 1 * D 0 3 := by rfl

theorem minorFormula_at_44 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (44 : Fin 70) =
      D 0 2 * D 3 3 - D 3 2 * D 0 3 := by rfl

theorem minorFormula_at_45 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (45 : Fin 70) =
      -D 0 0 * D 2 1 + D 2 0 * D 0 1 := by rfl

theorem minorFormula_at_46 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (46 : Fin 70) =
      -D 0 0 * D 2 2 + D 2 0 * D 0 2 := by rfl

theorem minorFormula_at_47 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (47 : Fin 70) =
      -D 0 0 * D 2 3 + D 2 0 * D 0 3 := by rfl

theorem minorFormula_at_48 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (48 : Fin 70) =
      -D 0 1 * D 2 2 + D 2 1 * D 0 2 := by rfl

theorem minorFormula_at_49 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (49 : Fin 70) =
      -D 0 1 * D 2 3 + D 2 1 * D 0 3 := by rfl

theorem minorFormula_at_50 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (50 : Fin 70) =
      -D 0 2 * D 2 3 + D 2 2 * D 0 3 := by rfl

theorem minorFormula_at_51 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (51 : Fin 70) =
      -D 0 0 * D 2 1 * D 3 2 + D 0 0 * D 3 1 * D 2 2 + D 2 0 * D 0 1 * D 3 2 - D 2 0 * D 3 1 * D 0 2 - D 3 0 * D 0 1 * D 2 2 + D 3 0 * D 2 1 * D 0 2 := by rfl

theorem minorFormula_at_52 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (52 : Fin 70) =
      -D 0 0 * D 2 1 * D 3 3 + D 0 0 * D 3 1 * D 2 3 + D 2 0 * D 0 1 * D 3 3 - D 2 0 * D 3 1 * D 0 3 - D 3 0 * D 0 1 * D 2 3 + D 3 0 * D 2 1 * D 0 3 := by rfl

theorem minorFormula_at_53 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (53 : Fin 70) =
      -D 0 0 * D 2 2 * D 3 3 + D 0 0 * D 3 2 * D 2 3 + D 2 0 * D 0 2 * D 3 3 - D 2 0 * D 3 2 * D 0 3 - D 3 0 * D 0 2 * D 2 3 + D 3 0 * D 2 2 * D 0 3 := by rfl

theorem minorFormula_at_54 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (54 : Fin 70) =
      -D 0 1 * D 2 2 * D 3 3 + D 0 1 * D 3 2 * D 2 3 + D 2 1 * D 0 2 * D 3 3 - D 2 1 * D 3 2 * D 0 3 - D 3 1 * D 0 2 * D 2 3 + D 3 1 * D 2 2 * D 0 3 := by rfl

theorem minorFormula_at_55 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (55 : Fin 70) =
      D 0 0 * D 1 1 - D 1 0 * D 0 1 := by rfl

theorem minorFormula_at_56 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (56 : Fin 70) =
      D 0 0 * D 1 2 - D 1 0 * D 0 2 := by rfl

theorem minorFormula_at_57 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (57 : Fin 70) =
      D 0 0 * D 1 3 - D 1 0 * D 0 3 := by rfl

theorem minorFormula_at_58 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (58 : Fin 70) =
      D 0 1 * D 1 2 - D 1 1 * D 0 2 := by rfl

theorem minorFormula_at_59 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (59 : Fin 70) =
      D 0 1 * D 1 3 - D 1 1 * D 0 3 := by rfl

theorem minorFormula_at_60 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (60 : Fin 70) =
      D 0 2 * D 1 3 - D 1 2 * D 0 3 := by rfl

theorem minorFormula_at_61 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (61 : Fin 70) =
      D 0 0 * D 1 1 * D 3 2 - D 0 0 * D 3 1 * D 1 2 - D 1 0 * D 0 1 * D 3 2 + D 1 0 * D 3 1 * D 0 2 + D 3 0 * D 0 1 * D 1 2 - D 3 0 * D 1 1 * D 0 2 := by rfl

theorem minorFormula_at_62 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (62 : Fin 70) =
      D 0 0 * D 1 1 * D 3 3 - D 0 0 * D 3 1 * D 1 3 - D 1 0 * D 0 1 * D 3 3 + D 1 0 * D 3 1 * D 0 3 + D 3 0 * D 0 1 * D 1 3 - D 3 0 * D 1 1 * D 0 3 := by rfl

theorem minorFormula_at_63 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (63 : Fin 70) =
      D 0 0 * D 1 2 * D 3 3 - D 0 0 * D 3 2 * D 1 3 - D 1 0 * D 0 2 * D 3 3 + D 1 0 * D 3 2 * D 0 3 + D 3 0 * D 0 2 * D 1 3 - D 3 0 * D 1 2 * D 0 3 := by rfl

theorem minorFormula_at_64 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (64 : Fin 70) =
      D 0 1 * D 1 2 * D 3 3 - D 0 1 * D 3 2 * D 1 3 - D 1 1 * D 0 2 * D 3 3 + D 1 1 * D 3 2 * D 0 3 + D 3 1 * D 0 2 * D 1 3 - D 3 1 * D 1 2 * D 0 3 := by rfl

theorem minorFormula_at_65 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (65 : Fin 70) =
      -D 0 0 * D 1 1 * D 2 2 + D 0 0 * D 2 1 * D 1 2 + D 1 0 * D 0 1 * D 2 2 - D 1 0 * D 2 1 * D 0 2 - D 2 0 * D 0 1 * D 1 2 + D 2 0 * D 1 1 * D 0 2 := by rfl

theorem minorFormula_at_66 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (66 : Fin 70) =
      -D 0 0 * D 1 1 * D 2 3 + D 0 0 * D 2 1 * D 1 3 + D 1 0 * D 0 1 * D 2 3 - D 1 0 * D 2 1 * D 0 3 - D 2 0 * D 0 1 * D 1 3 + D 2 0 * D 1 1 * D 0 3 := by rfl

theorem minorFormula_at_67 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (67 : Fin 70) =
      -D 0 0 * D 1 2 * D 2 3 + D 0 0 * D 2 2 * D 1 3 + D 1 0 * D 0 2 * D 2 3 - D 1 0 * D 2 2 * D 0 3 - D 2 0 * D 0 2 * D 1 3 + D 2 0 * D 1 2 * D 0 3 := by rfl

theorem minorFormula_at_68 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (68 : Fin 70) =
      -D 0 1 * D 1 2 * D 2 3 + D 0 1 * D 2 2 * D 1 3 + D 1 1 * D 0 2 * D 2 3 - D 1 1 * D 2 2 * D 0 3 - D 2 1 * D 0 2 * D 1 3 + D 2 1 * D 1 2 * D 0 3 := by rfl

theorem minorFormula_at_69 {R : Type*} [CommRing R]
    (D : Coordinate → Coordinate → R) : minorFormula D (69 : Fin 70) =
      D 0 0 * D 1 1 * D 2 2 * D 3 3 - D 0 0 * D 1 1 * D 3 2 * D 2 3 - D 0 0 * D 2 1 * D 1 2 * D 3 3 + D 0 0 * D 2 1 * D 3 2 * D 1 3 + D 0 0 * D 3 1 * D 1 2 * D 2 3 - D 0 0 * D 3 1 * D 2 2 * D 1 3 - D 1 0 * D 0 1 * D 2 2 * D 3 3 + D 1 0 * D 0 1 * D 3 2 * D 2 3 + D 1 0 * D 2 1 * D 0 2 * D 3 3 - D 1 0 * D 2 1 * D 3 2 * D 0 3 - D 1 0 * D 3 1 * D 0 2 * D 2 3 + D 1 0 * D 3 1 * D 2 2 * D 0 3 + D 2 0 * D 0 1 * D 1 2 * D 3 3 - D 2 0 * D 0 1 * D 3 2 * D 1 3 - D 2 0 * D 1 1 * D 0 2 * D 3 3 + D 2 0 * D 1 1 * D 3 2 * D 0 3 + D 2 0 * D 3 1 * D 0 2 * D 1 3 - D 2 0 * D 3 1 * D 1 2 * D 0 3 - D 3 0 * D 0 1 * D 1 2 * D 2 3 + D 3 0 * D 0 1 * D 2 2 * D 1 3 + D 3 0 * D 1 1 * D 0 2 * D 2 3 - D 3 0 * D 1 1 * D 2 2 * D 0 3 - D 3 0 * D 2 1 * D 0 2 * D 1 3 + D 3 0 * D 2 1 * D 1 2 * D 0 3 := by rfl

end Papers.RationalityTen.MatroidChecked.ChartPolynomial
