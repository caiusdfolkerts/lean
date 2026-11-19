module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots28

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row28.offset : Nat :=
23485
def Papers.RationalityTen.SharedEmptyKeys.Row28.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row28.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row28.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row28.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row28.offset + i) =
      (28,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row28.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row28.rootCount i))))

