(* BEGIN FIX *)
Parameter (Ty : Type).
Parameter (Tm : Ty -> Type).

Parameter arr  : Ty -> Ty -> Ty.
Notation "x ⇒ y" := (arr x y) (at level 80, right associativity).
Parameter app  : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y" := (app x y) (at level 50, left associativity).
Parameter lam  : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 51, x name).
Parameter arrβ : forall {A B : Ty} {b : Tm A -> Tm B} {a : Tm A}, lam b ⋅ a = b a.
Parameter arrη : forall {A B : Ty} {f : Tm (A ⇒ B)}, f = λ x, f ⋅ x.

Parameter (Nat : Ty).
Parameter (zero   : Tm Nat).
Parameter (suc    : Tm Nat -> Tm Nat).
Parameter (ite    : forall {A}, Tm A -> (Tm A -> Tm A) -> Tm Nat -> Tm A).
Parameter (Natβ₁  : forall {A} {z : Tm A} {s : Tm A -> Tm A}, ite z s zero = z).
Parameter (Natβ₂  : forall {A} {z : Tm A} {s : Tm A -> Tm A} {u : Tm Nat}, ite z s (suc u) = s (ite z s u)).

Definition one   : Tm Nat := suc zero.
Definition two   : Tm Nat := suc one.
Definition three : Tm Nat := suc two.
Definition four  : Tm Nat := suc three.
Definition seven : Tm Nat := suc (suc (suc four)).

(* Definition double : Tm (Nat ⇒ Nat) := lam (fun x => ite zero (fun y => suc (suc y)) x). *)
Definition doubleplustwo : Tm (Nat ⇒ Nat) :=
(* END FIX *)
lam (fun x => suc (suc (ite zero (fun y => suc (suc y)) x)))
(*   lam (fun x => suc (suc x)) *)
(* BEGIN FIX *)
.

Fixpoint quote (n : nat) : Tm Nat :=
  match n with
  | O => zero
  | S n => suc (quote n)
  end.

Definition defines (t : Tm (Nat ⇒ Nat)) (f : nat -> nat) := forall n, t ⋅ quote n = quote (f n).
Definition definable (f : nat -> nat) := exists (t : Tm (Nat ⇒ Nat)), defines t f.

Lemma doubleplustwoCorrect : defines doubleplustwo (fun n => 2 * n + 2).
Proof.
(* END FIX *)
  unfold defines, doubleplustwo, two, one.
  intro.
  rewrite ! arrβ.
  simpl.
  induction n ; simpl.
  rewrite ! Natβ₁.
  reflexivity.
  rewrite ! Natβ₂.
  rewrite IHn.
  now rewrite <- (plus_n_Sm n (n + 0)).
(* BEGIN FIX *)
Qed.

Goal definable (fun n => 2 * n + 2).
Proof.
  exists doubleplustwo. exact doubleplustwoCorrect.
Qed.
(* END FIX *)