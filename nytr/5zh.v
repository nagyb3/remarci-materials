(* BEGIN FIX *)
Inductive Ty : Type := 
 | Nat  : Ty
 | arr  : Ty -> Ty -> Ty.
Notation "x ⇒ y" := (arr x y) (at level 80, right associativity).

Parameter (Tm : Ty -> Type).

Parameter app  : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y" := (app x y) (at level 50, left associativity).
Parameter lam  : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 51, x name, only parsing).
Parameter arrβ : forall {A B : Ty} (b : Tm A -> Tm B)(a : Tm A), lam b ⋅ a = b a.
Parameter arrη : forall {A B : Ty} (f : Tm (A ⇒ B)), f = λ x, f ⋅ x.

Parameter (zero : Tm Nat).
Parameter (suc  : Tm Nat -> Tm Nat).

Definition one   : Tm Nat := suc zero.
Definition two   : Tm Nat := suc one.
Definition three : Tm Nat := suc two.
Definition four  : Tm Nat := suc three.
Definition seven : Tm Nat := suc (suc (suc four)).

Fixpoint quote (n : nat) : Tm Nat :=
  match n with
  | O => zero
  | S n => suc (quote n)
  end.

Parameter (iter  : forall {A}, Tm A -> (Tm A -> Tm A) -> Tm Nat -> Tm A).
Parameter (Natβ₁ : forall {A z s},   @iter A z s zero = z).
Parameter (Natβ₂ : forall {A z s u}, @iter A z s (suc u) = s (iter z s u)).

Definition Bool  : Ty := Nat.
Definition false : Tm Bool := zero.
Definition true  : Tm Bool := one.
Definition ite {A : Ty} (b : Tm Bool) (u v : Tm A) : Tm A := iter v (fun _ => u) b.
Lemma iteβ₁ : forall A (u v : Tm A), ite true u v = u.
Proof.
  intros. cbv. rewrite Natβ₂. reflexivity.
Qed.
Lemma iteβ₂ : forall A (u v : Tm A), ite false u v = v.
Proof.
  intros. cbv. rewrite Natβ₁. reflexivity.
Qed.

Definition and : Tm (Bool ⇒ Bool ⇒ Bool) := λ a, λ b, ite a b false.

Goal and ⋅ true ⋅ false = false.
Proof.
(* END FIX *)
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₂.
  reflexivity.
(* BEGIN FIX *)
Qed.
(* END FIX *)