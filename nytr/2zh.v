(* BEGIN FIX *)
Module RazorEquationalTheory.
  Declare Scope razor_scope.
  Delimit Scope razor_scope with razor.
  Open Scope razor_scope.

  Parameter (Ty   : Type).
  Parameter (Bool : Ty).
  Parameter (Nat  : Ty).

  Parameter (Tm : Ty -> Type).
  Parameter (true   : Tm Bool).
  Parameter (false  : Tm Bool).
  Parameter (ite    : forall {A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A).
  Parameter (num    : nat -> Tm Nat).
  Parameter (isZero : Tm Nat -> Tm Bool).
  Parameter (plus   : Tm Nat -> Tm Nat -> Tm Nat).
  Bind Scope razor_scope with Tm.
  Notation "x + y" := (plus x y) (at level 50, left associativity) : razor_scope.

  Parameter (iteβ₁    : forall {A} {u v : Tm A}, ite true u v = u).
  Parameter (iteβ₂    : forall {A} {u v : Tm A}, ite false u v = v).
  Parameter (isZeroβ₁ : isZero (num 0) = true).
  Parameter (isZeroβ₂ : forall {n}, isZero (num (S n)) = false).
  Parameter (plusβ    : forall {m n}, plus (num m) (num n) = num (m + n)).
  (* \beta = β                    \_1 = ₁                    \_2 = ₂ *)

  Goal ite (isZero (num 5)) (num 30) (num 27) + ite (isZero (num 0)) (num 42) (num 5) = num 69.
  Proof.
(* END FIX *)
  simpl.
  rewrite isZeroβ₁.
  rewrite isZeroβ₂.
  rewrite iteβ₁.
  rewrite iteβ₂.
  rewrite plusβ.
  simpl.
  reflexivity.
(* BEGIN FIX *)
  Qed.
End RazorEquationalTheory.
(* END FIX *)