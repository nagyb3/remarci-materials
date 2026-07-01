(* BEGIN FIX *)
Module STLC.

Declare Scope razor_scope.
Delimit Scope razor_scope with razor.

Parameter (Ty   : Type).
Parameter (Bool : Ty).
Parameter (Nat  : Ty).

Parameter (Tm : Ty -> Type).
Parameter (true   : Tm Bool).
Parameter (false  : Tm Bool).
Parameter (ite    : forall{A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A).
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

Parameter arr  : Ty -> Ty -> Ty.
Notation "x ⇒ y" := (arr x y) (at level 80, right associativity).
(* \Rightarrow = ⇒ *)

Parameter app  : forall {A B : Ty}, Tm (A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y" := (app x y) (at level 50, left associativity).
(* \cdot = ⋅ *)
Parameter lam  : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 51, x name, only parsing).
(* \lambda = λ *)

Parameter arrβ : forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a.
Parameter arrη : forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun x => f ⋅ x).

Definition alma {A B C : Ty} : Tm ((B ⇒ A ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) :=
(* END FIX *)

  lam (fun f => lam (fun g => lam (fun h =>f ⋅ (g ⋅ h) ⋅ h)))








   
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
(*   lam (fun f => lam (fun g => lam (fun x => f ⋅ (g ⋅ x) ⋅ x))) *)
(* BEGIN FIX *)
.

Goal forall A B C (f : Tm (B ⇒ A ⇒ C)) (g : Tm (A ⇒ B)) (x : Tm A), alma ⋅ f ⋅ g ⋅ x = f ⋅ (g ⋅ x) ⋅ x.
Proof.
(* END FIX *)
  intros.
  cbv.
  rewrite ! arrβ.
  reflexivity.
(* BEGIN FIX *)
Qed.

End STLC.
(* END FIX *)