(* BEGIN FIX *)
Module U.

  Inductive Tm : Type :=
    | true   : Tm
    | false  : Tm
    | ite    : Tm -> Tm -> Tm -> Tm
    | num    : nat -> Tm
    | isZero : Tm -> Tm
    | plus   : Tm -> Tm -> Tm
  .

End U.

Module T.

  Inductive Ty : Type := Bool | Nat.

  Inductive Tm : Ty -> Type :=
    | true   : Tm Bool
    | false  : Tm Bool
    | ite    : forall {A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A
    | num    : nat -> Tm Nat
    | isZero : Tm Nat -> Tm Bool
    | plus   : Tm Nat -> Tm Nat -> Tm Nat
  .

  Fixpoint erase {A : Ty} (a : Tm A) : U.Tm :=
    match a with
    | true => U.true
    | false => U.false
    | ite t u v => U.ite (erase t) (erase u) (erase v)
    | num n => U.num n
    | isZero t => U.isZero (erase t)
    | plus u v => (U.plus (erase u) (erase v))
    end.

  Fixpoint infer (a : U.Tm) : option {A : Ty & Tm A} :=
    match a with
    | U.true  => Some (existT _ Bool true)
    | U.false => Some (existT _ Bool false)
    | U.ite t u v =>
      match infer t, infer u, infer v with
      | Some (existT _ Bool t'),
        Some (existT _ Nat  u'),
        Some (existT _ Nat  v') =>
          Some (existT _ Nat (ite t' u' v'))
      | Some (existT _ Bool t'),
        Some (existT _ Bool u'),
        Some (existT _ Bool v') =>
          Some (existT _ Bool (ite t' u' v'))
      | _, _, _ => None
      end
    | U.num n => Some (existT _ Nat (num n))
    | U.isZero t =>
      match infer t with
      | Some (existT _ Nat t') => Some (existT _ Bool (isZero t'))
      | _ => None
      end
    | U.plus u v => 
      match infer u, infer v with
      | Some (existT _ Nat u'),
        Some (existT _ Nat v') =>
          Some (existT _ Nat (plus u' v'))
      | _, _ => None
      end
    end.

  Goal exists A t, infer (U.ite (U.isZero (U.num 2)) (U.isZero (U.plus (U.num 1) (U.num 2))) (U.isZero (U.num 0))) = Some (existT _ A t).
  Proof.
(* END FIX *)
  exists Bool.
  exists (ite (isZero (num 2)) (isZero (plus (num 1) (num 2))) (isZero (num 0))).
  simpl. reflexivity.
(* BEGIN FIX *)
  Qed.

End T.
(* END FIX *)