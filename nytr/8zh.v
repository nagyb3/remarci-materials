(* BEGIN FIX *)
Parameter Ty : Type.

Parameter Prod   :  Ty -> Ty -> Ty.
Notation "A × B" := (Prod A B) (at level 78, right associativity). (* \times *)

Parameter Unit  :  Ty.
Notation "⊤"    := Unit. (* \top *)

Parameter Sum    :  Ty -> Ty -> Ty.
Notation "A ⊎ B" := (Sum A B) (at level 79, right associativity). (* \uplus *)

Parameter Empty :  Ty.
Notation "⊥"    := Empty. (* \bot *)

Inductive Poly : (Ty -> Ty) -> Type :=
  | idPoly    : Poly (fun X => X)
  | ProdPoly  : forall {F G}, Poly F -> Poly G -> Poly (fun X => F X × G X)
  | UnitPoly  : Poly (fun X => ⊤)
  | SumPoly   : forall {F G}, Poly F -> Poly G -> Poly (fun X => F X ⊎ G X)
  | EmptyPoly : Poly (fun X => ⊥)
.

(* Emlékeztetőül, a műveleti sorrend: összeadás < szorzás < konstansok (X, 1/⊤, 0/⊥). *)

(*                        3      *       x^4        +     2    *     x^3      +  0 *   x^2    + x +    2   *)
Goal Poly (fun X => ((⊤ ⊎ ⊤ ⊎ ⊤) × (X × X × X × X)) ⊎ ((⊤ ⊎ ⊤) × (X × X × X)) ⊎ (⊥ × (X × X)) ⊎ X ⊎ (⊤ ⊎ ⊤)).
Proof.
(* END FIX *)
  (* Ezt ki lehet venni kommentből, ha úgy könnyebb: *)
  Unset Printing Notations.
  apply SumPoly.
  apply ProdPoly.
  apply SumPoly.
  apply UnitPoly.
  apply SumPoly.
  apply UnitPoly.
  apply UnitPoly.
  apply ProdPoly.
  apply idPoly.
  apply ProdPoly.
  apply idPoly.
  apply ProdPoly.
  apply idPoly.
  apply idPoly.
  apply SumPoly.
  apply ProdPoly.
  apply SumPoly.
  apply UnitPoly.
  apply UnitPoly.
  apply ProdPoly.
  apply idPoly.
  apply ProdPoly.
  apply idPoly.
  apply idPoly.
  apply SumPoly.
  apply ProdPoly.
  apply EmptyPoly.
  apply ProdPoly.
  apply idPoly.
  apply idPoly.
  apply SumPoly.
  apply idPoly.
  apply SumPoly.
  apply UnitPoly.
  apply UnitPoly.
(* BEGIN FIX *)
Qed.
(* END FIX *)