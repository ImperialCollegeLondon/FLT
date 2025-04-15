import Mathlib
import Mathlib.Algebra.Group.Units.Hom

variable {R R' : Type*} [CommRing R] [CommRing R'] (I : Ideal R) [Nontrivial (R ⧸ I)] [IsLocalRing R] [IsLocalRing R']

instance IsLocalHom.quotient_mk :
  IsLocalHom (algebraMap R (R ⧸ I)) := .of_surjective _ Ideal.Quotient.mk_surjective

instance IsLocalHom.of_quotient (f : R →+* R') [IsLocalHom f] (J : Ideal R') [Nontrivial (R' ⧸ J)] :
    IsLocalHom (RingHom.comp (algebraMap R' (R' ⧸ J)) f) :=
  RingHom.isLocalHom_comp (algebraMap R' (R' ⧸ J)) f
