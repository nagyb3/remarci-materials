Require Import FunctionalExtensionality.

Module RazorEvaluator.

Declare Scope razor_scope.
Delimit Scope razor_scope with razor.

Inductive Ty : Type := Bool | Nat.

Inductive Tm : Ty -> Type :=
  | true   : Tm Bool
  | false  : Tm Bool
  | ite    : forall{A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A
  | num    : nat -> Tm Nat
  | isZero : Tm Nat -> Tm Bool
  | plus   : Tm Nat -> Tm Nat -> Tm Nat
.
Bind Scope razor_scope with Tm.
Notation "x + y" := (plus x y) (at level 50, left associativity) : razor_scope.

Definition evalTy (A : Ty) : Type := match A with
                                     | Nat => nat
                                     | Bool => bool
                                     end.

(*
Fixpoint eval (t : Tm) : nat :=
  match t with
  | true => 1
  | false => 0
  | ite t u v => match (eval t) with
                 | 0 => eval v
                 | _ => eval u
                 end
  | num n => n
  | isZero t => match eval t with
                | 0 => 1
                | _ => 0
                end
  | plus t u => eval t + eval u
  end.
*)

(* EXE: write a type-correct evaluator *)
Fixpoint evalTm {A : Ty} (t : Tm A) : evalTy A :=
  match t with
  | true => Datatypes.true
  | false => Datatypes.false
  | ite t u v => if evalTm t
                 then evalTm u
                 else evalTm v
  | num n => n
  | isZero t => match evalTm t with
                | 0 => Datatypes.true
                | _ => Datatypes.false
                end
  | plus t u => evalTm t + evalTm u
  end.

(* EXE *)
Example notEq : exists A : Ty, exists t1 t2 : Tm A, ~ t1 = t2 /\ evalTm t1 = evalTm t2.
Proof.
  exists Nat.
  exists (num 1).
  exists (plus (num 0) (num 1)).
  simpl.
  split.
  * unfold not. discriminate.
  * reflexivity.
Qed.

(* the evaluator satisfies the following equations: *)

Lemma iteβ₁    : forall {A} {u v : Tm A}, evalTm (ite true u v) = evalTm u.
Proof.
  intros.
  simpl. reflexivity.
Qed.
Lemma iteβ₂    : forall {A} {u v : Tm A}, evalTm (ite false u v) = evalTm v.
Proof.
  intros.
  simpl. reflexivity.
Qed.
Lemma isZeroβ₁ : evalTm (isZero (num 0)) = evalTm true.
Proof.
  simpl. reflexivity.
Qed.
Lemma isZeroβ₂ : forall {n}, evalTm (isZero (num (S n))) = evalTm false.
Proof.
  intros.
  simpl. reflexivity.
Qed.
Lemma plusβ    : forall {m n}, evalTm (plus (num m) (num n)) = evalTm (num (m + n)).
Proof.
  intros.
  simpl. reflexivity.
Qed.

End RazorEvaluator.

Module RazorEquationalTheory.
(**
  The equational theory explains how to run programs, which programs are equal.
*)

Declare Scope razor_scope.
Delimit Scope razor_scope with razor.

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

(* semantical equations *)
Parameter (iteβ₁    : forall {A} {u v : Tm A}, ite true u v = u).
Parameter (iteβ₂    : forall {A} {u v : Tm A}, ite false u v = v).
Parameter (isZeroβ₁ : isZero (num 0) = true).
Parameter (isZeroβ₂ : forall {n}, isZero (num (S n)) = false).
Parameter (plusβ    : forall {m n}, plus (num m) (num n) = num (m + n)).
(*
  \beta = β
  \_1 = ₁
  \_2 = ₂
*)

(* Set Printing All. *)

(* EXE *)
Goal ite (isZero (num 0 + num 1)) false (isZero (num 0)) = true.
Proof.
  rewrite plusβ.
  simpl.
  rewrite isZeroβ₂.
  rewrite isZeroβ₁.
  rewrite iteβ₂.
  reflexivity.
Qed.

(* EXE *)
Goal exists n, ite (isZero (num 0 + num 0)) (num 10) (num 20) = num n.
Proof.
  exists 10.
  rewrite plusβ.
  simpl.
  rewrite isZeroβ₁.
  rewrite iteβ₁.
  reflexivity.
Qed.

(* EXE *)
Goal forall n t, ite (isZero (num 0 + num 0)) (num 0 + num n) t = num n.
Proof.
  intros.
  rewrite plusβ.
  simpl.
  rewrite isZeroβ₁.
  rewrite iteβ₁.
  rewrite plusβ.
  simpl.
  reflexivity.
Qed.

(* EXE *)
Goal true = false -> forall (A : Ty) (a a' : Tm A), a = a'.
Proof.
  intros.
  Fail discriminate H.
  About f_equal.
  apply (f_equal (fun x => ite x a a')) in H.
  rewrite iteβ₁, iteβ₂ in H.
  exact H. (* assumption. *)
Defined tneqf.
  
(* EXE *)
Goal num 0 = num 1 -> forall (A : Ty) (a a' : Tm A), a = a'.
Proof.
  intros.
  apply (f_equal isZero) in H.
  rewrite isZeroβ₁, isZeroβ₂ in H.
  eapply tneqf in H.
  exact H. (* eassumption. *)
Qed.

(* Coq: Kukurikú? 🐓 *)

Parameter (isOne : Tm Nat -> Tm Bool).
Parameter (isOneβ₁ : isOne (num 0) = false).
Parameter (isOneβ₂ : isOne (num 1) = true).
Parameter (isOneβ_kiscica : forall {n}, isOne (num (S (S n))) = false).

(* EXE: can we prove this?
   If yes, prove it!
   If not, how do we change the language so that it can be proven? *)
Goal num 1 = num 2 -> forall (A : Ty) (a a' : Tm A), a = a'.
Proof.
  (* Nah bro, not possible :( *)
  (* Hol' up, what about isOne? *)
  intros.
  apply (f_equal isOne) in H.
  rewrite isOneβ₂, isOneβ_kiscica in H.
  apply tneqf. assumption.
Qed.

End RazorEquationalTheory.

Module STLC.

(* For simply typed lambda calculus (Razor extended with functions) we
only define the well-typed representation with the equational
theory. *)

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

(* new stuff: *)
Parameter arr  : Ty -> Ty -> Ty.
Notation "x ⇒ y" := (arr x y) (at level 80, right associativity).

Parameter app  : forall {A B : Ty}, Tm (A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y" := (app x y) (at level 50, left associativity).
Parameter lam  : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).

Parameter arrβ : forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a.
Parameter arrη : forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun x => f ⋅ x).

(* draw the derivation tree *)
Definition add2 : Tm (Nat ⇒ Nat) := lam (fun x => plus x (num 2)).
Goal add2 ⋅ num 3 = num 5.
Proof.
  
  cbn.
  simpl.
Admitted.

(* draw the derivation tree *)
Definition apply2x : Tm ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat). Admitted.
Goal apply2x ⋅ add2 ⋅ num 0 = num 4.
Proof.
Admitted.
Goal apply2x ⋅ add2 ⋅ num 3 = num 7.
Proof.
Admitted.

(* draw the derivation tree *)
Definition K {A B : Ty} : Tm (A ⇒ B ⇒ A). Admitted.
Goal forall {A B : Ty} {u : Tm A} {f : Tm B}, K ⋅ u ⋅ f = u.
Proof.
Admitted.

(* draw the derivation tree *)
Definition join {A B : Ty} : Tm ((A ⇒ A ⇒ B) ⇒ A ⇒ B). Admitted.
Goal forall {A B : Ty} {f : Tm (A ⇒ A ⇒ B)} {u : Tm A}, join ⋅ f ⋅ u = f ⋅ u ⋅ u.
Proof.
Admitted.

(* draw the derivation tree *)
Definition S {A B C : Ty} : Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) := lam (fun f => lam (fun g => lam (fun a => f ⋅ a ⋅ (g ⋅ a)))).
Goal forall {A B C : Ty} {f : Tm(A ⇒ B ⇒ C)} {g : Tm(A ⇒ B)} {u : Tm A}, S ⋅ f ⋅ g ⋅ u = f ⋅ u ⋅ (g ⋅ u).
Proof.
Admitted.

(* draw the derivation tree *)
Definition someTerm (A P Q : Ty) : Tm ((A ⇒ Q) ⇒ ((((P ⇒ Q) ⇒ P) ⇒ P) ⇒ A) ⇒ A). Admitted.

Definition neg : Tm (Bool ⇒ Bool) := lam (fun b => ite b false true).
Goal neg ⋅ true = false.
Proof.
Admitted.
Goal neg ⋅ false = true.
Proof.
Admitted.

Definition and : Tm (Bool ⇒ Bool ⇒ Bool).  Admitted.  (* λ b c . ite b (ite c true false) (ite c false false) *)

Definition and' : Tm (Bool ⇒ Bool ⇒ Bool). Admitted. (* λ b c . ite b c false *)

Goal and  ⋅ true ⋅ false = false.
Proof.
Admitted.
Goal and' ⋅ true ⋅ false = false.
Proof.
Admitted.
Goal and  ⋅ true ⋅ true = true.
Proof.
Admitted.
Goal and' ⋅ true ⋅ true = true.
Proof.
Admitted.
Goal forall (b : Tm Bool), and' ⋅ true ⋅ b = b.
Proof.
Admitted.

Goal forall b, and' ⋅ b ⋅ false = false.
Proof.
Admitted.

(*
   The following Goal is not provable by itself. Explain why that is.
   Try again after uncommenting the axiom below.
 *)

(* Axiom Boolη : forall (b : Tm Bool), b = true \/ b = false. *)

Goal forall a b, and ⋅ a ⋅ b = and ⋅ b ⋅ a.
Proof.
Admitted.

Definition or : Tm (Bool ⇒ Bool ⇒ Bool). Admitted.
Goal forall b, or ⋅ true ⋅ b = true.
Proof.
Admitted.
Goal forall b, or ⋅ false ⋅ b = b.
Proof.
Admitted.

(* Same situation as above. Explain why it's not provable, then try with uncommenting Boolη. *)

Goal forall a b, or ⋅ a ⋅ b = or ⋅ b ⋅ a.
Proof.
Admitted.

(* for every type A, Tm (A ⇒ A) is a monoid *)
Definition comp' {A} : Tm ((A ⇒ A) ⇒ (A ⇒ A) ⇒ (A ⇒ A)) :=
  lam (fun f => lam (fun g => lam (fun x => f ⋅ (g ⋅ x)))).
Notation "f ⊚ g" := (comp' ⋅ f ⋅ g) (at level 50, left associativity). (* \ocir = ⊚ *)
Definition id {A} : Tm (A ⇒ A) := lam (fun a => a).

Goal forall A (f g h : Tm (A ⇒ A)), (f ⊚ g) ⊚ h = f ⊚ (g ⊚ h).
Proof.
Admitted.

Goal forall A (f : Tm (A ⇒ A)), f ⊚ id = f.
Proof.
Admitted.

Goal forall A (f : Tm (A ⇒ A)), id ⊚ f = f.
Proof.
Admitted.

(* types form a category *)
Definition comp {A B C} : Tm ((B ⇒ A) ⇒ (C ⇒ B) ⇒ (C ⇒ A)) :=
  lam (fun f => lam (fun g => lam (fun x => f ⋅ (g ⋅ x)))).
Notation "f ∘ g" := (comp ⋅ f ⋅ g) (at level 40, left associativity). (* \circ *)

Goal forall A B C D (f : Tm (B ⇒ A))(g : Tm (C ⇒ B))(h : Tm (D ⇒ C)), (f ∘ g) ∘ h = f ∘ (g ∘ h).
Proof.
Admitted.
Goal forall A B (f : Tm (B ⇒ A)), id ∘ f = f.
Proof.
Admitted.
Goal forall A B (f : Tm (B ⇒ A)), f ∘ id = f.
Proof.
Admitted.

End STLC.

