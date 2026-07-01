Require Import Nat.

Module SystemT_with_ite.

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

(* Unset Printing Notations. About arrη. *)

Parameter (Nat : Ty).
Parameter (zero   : Tm Nat).
Parameter (suc    : Tm Nat -> Tm Nat).
(* iteration on Nat *)
Parameter (ite    : forall {A}, Tm A -> (Tm A -> Tm A) -> Tm Nat -> Tm A).
Parameter (Natβ₁  : forall {A} {z : Tm A} {s : Tm A -> Tm A}, ite z s zero = z).
Parameter (Natβ₂  : forall {A} {z : Tm A} {s : Tm A -> Tm A} {u : Tm Nat}, ite z s (suc u) = s (ite z s u)).

(*
  ----------
  zero : Nat

    n : Nat
  -----------
  suc n : Nat

  z : A    x : A |- s : A    n : Nat
  ----------------------------------
            ite z s n : A
 *)

Definition one   : Tm Nat := suc zero.
Definition two   : Tm Nat := suc one.
Definition three : Tm Nat := suc two.
Definition four  : Tm Nat := suc three.
Definition seven : Tm Nat := suc (suc (suc four)).
Definition eight : Tm Nat := suc seven.

(*
       ----------
       zero : Nat
     --------------
     suc zero : Nat
  --------------------
  suc (suc zero) : Nat
 *)

Goal forall A z s, @ite A z s (suc (suc zero)) = s (s z) .
Proof.
  intros.
  rewrite Natβ₂.
  rewrite Natβ₂.
  rewrite Natβ₁.
  reflexivity.
  Restart. intros.
  now rewrite ! Natβ₂, Natβ₁.
Qed.

(*
  ite z s (suc (suc zero)) =(Natβ₂)
  s (ite z s (suc zero))   =(Natβ₂)
  s (s (ite z s zero))     =(Natβ₁)
  s (s z)
*)

(*
















   -------------------------------------------------------------------------------------------------------------------------------------------

                                                                                                                                   : Nat ⇒ Nat

 *)

Definition double : Tm (Nat ⇒ Nat) := λ x, ite zero (fun y => suc (suc y)) x. 
Goal double ⋅ four = eight.
Proof.
  cbv.
  rewrite arrβ.
  rewrite ! Natβ₂, Natβ₁.
  reflexivity.
Qed.

(* Ágyazzuk be a természetes számokat a nyelvbe *)
Fixpoint quote (n : nat) : Tm Nat :=
  match n with
  | O => zero
  | S n => suc (quote n)
  end.

Lemma doubleCorrect : forall (n : nat), double ⋅ quote n = quote (2 * n).
Proof.
  intros.
  unfold double.
  simpl.
  rewrite ! arrβ.
  induction n ; simpl.
  * rewrite Natβ₁. reflexivity.
  * rewrite Natβ₂. rewrite IHn.
    Search (_ + S _).
    About plus_n_Sm.
    rewrite <- plus_n_Sm. simpl. reflexivity.
Qed.

(* A function f is definable in System T if there is a term which computes to f n on any n *)
Definition defines (t : Tm (Nat ⇒ Nat)) (f : nat -> nat) := forall n, t ⋅ quote n = quote (f n).

(* Notation "t ≈ f" := (defines t f) (at level 60). *)
(* Definition definable (f : nat -> nat) := exists (t : Tm (Nat ⇒ Nat)), t ≈ f. *)
(* Notation "⌈ f ⌉" := (definable f). *)

Definition definable (f : nat -> nat) := exists (t : Tm (Nat ⇒ Nat)), defines t f.

(* Goal ⌈ fun n => 2 * n ⌉. *)
Goal definable (fun n => 2 * n).
Proof.
  unfold definable, defines.
  exists double. exact doubleCorrect.
(*   unfold definable.
  exists double.
  unfold defines.
  intros.
  simpl.
  induction n ; simpl.
  * cbv. rewrite ! arrβ. rewrite Natβ₁. reflexivity.
  * simpl. rewrite <- IHn. rewrite <- plus_n_Sm. simpl.  unfold double. rewrite ! arrβ. rewrite ! Natβ₂. rewrite IHn. *)
Qed.

Definition plus1a : Tm (Nat ⇒ Nat) := lam (fun n => suc n).
(* Definition plus1a : Tm (Nat ⇒ Nat) := lam suc. *)

Goal defines plus1a S.
Proof.
  cbv -[quote].
  (* unfold defines, plus1a. *)
  intros.
  rewrite ! arrβ.
  simpl. reflexivity.
Qed.

(* ite *)
Definition plus1b : Tm (Nat ⇒ Nat) := lam (fun n => ite (suc zero) suc n).

Goal defines plus1b S.
Proof.
  unfold defines, plus1b.
  intros.
  rewrite ! arrβ.
  induction n ; simpl.
  * rewrite Natβ₁. reflexivity.
  * rewrite Natβ₂, IHn. simpl. reflexivity.
Qed.

Definition id_f : Tm (Nat ⇒ Nat) := lam (fun x => ite zero suc x).
(* Definition id_f : Tm (Nat ⇒ Nat) := lam (ite zero suc). *)

Definition defines2 (t : Tm (Nat ⇒ Nat ⇒ Nat)) (f : nat -> nat -> nat) :=
  forall n m, t ⋅ quote n ⋅ quote m = quote (f n m).

Definition definable2 (f : nat -> nat -> nat) := exists (t : Tm (Nat ⇒ Nat ⇒ Nat)), defines2 t f.

(* n =        suc (suc zero)
m =       suc (suc (suc zero))
n +m = suc (suc (suc (suc (suc (zero))))) *)

Definition addTm : Tm (Nat ⇒ Nat ⇒ Nat) := λ n, λ m, ite m suc n.
Definition addTm' : Tm (Nat ⇒ Nat ⇒ Nat) := λ n, λ m, ite n suc m.

Lemma addTmCorrect : defines2 addTm add.
Proof.
  unfold defines2, addTm.
  intros.
  rewrite ! arrβ.
  induction n ; simpl.
  * rewrite Natβ₁. reflexivity.
  * rewrite Natβ₂, IHn. reflexivity.
Qed.

Lemma addTm'Correct : defines2 addTm' add.
Proof.
  unfold defines2, addTm'.
  intros.
  rewrite ! arrβ.
  induction n ; simpl.
  * admit.
  * admit.
Admitted.

Goal definable2 add.
Proof.
  unfold definable2.
  exists addTm. exact addTmCorrect.
Qed.

(* n =        suc (suc zero)
n =        1 + 1 + 0
m =       suc (suc (suc zero))
m =       1 + 1 + 1 + 0
n + m = suc (suc (suc (suc (suc zero))))
n + m = 1 + 1 + 1 + 1 + 1 + 0 *)

Definition mulTm : Tm (Nat ⇒ Nat ⇒ Nat) := λ n, λ m, ite zero (fun o => addTm ⋅ m ⋅ o) n.

Goal definable2 mul.
Proof.
  exists mulTm. unfold defines2, mulTm.
  intros. rewrite 2 arrβ.
  induction n ; simpl.
  exact Natβ₁.
  rewrite Natβ₂, IHn.
  apply addTmCorrect.
Qed.

(* Ackermann function *)
Fixpoint ack (m n : nat) : nat :=
  match m with
  | O => 1 + n
  | S m' => let fix ackm (n : nat) :=
              match n with
              | O => ack m' 1
              | S n' => ack m' (ackm n')
              end in ackm n
  end.
Compute ack 0 0.
Compute ack 1 1.
Compute ack 2 2.
Compute ack 3 3.
(* Don't try this: Compute ack 4 4. *)
Compute ack 4 4.

(* short definition: ack' = ite suc (λ ackm . ite (ackm 1) ackm) *)
Definition ack' : Tm (Nat ⇒ Nat ⇒ Nat) :=
  lam (fun x => lam (fun y => ite (lam (fun x => suc x)) (fun ackm => lam (fun x => ite (ackm ⋅ one) (fun x => ackm ⋅ x) x)) x ⋅ y)).

Goal ack' ⋅ zero ⋅ zero = one.
Proof.
Admitted.
Goal ack' ⋅ one ⋅ one = three.
Proof.
Admitted.
Goal ack' ⋅ two ⋅ two = seven.
Proof.
Admitted.

(* hard: *)
Goal defines2 ack' ack.
Proof.
Admitted.

(* real equational consistency (we would need to do induction on the
syntax of System T) *)
Parameter eqCons : exists(A : Ty)(a a' : Tm A), a <> a'.
(* Parameter eqCons : exists(A : Ty)(a a' : Tm A), a = a' -> False. *)

(* weak form of equational consistency *)
Goal exists(A : Ty)(a a' : Tm A), a = a' -> forall(B : Ty)(b b' : Tm B), b = b'. Admitted.

(* we don't have logical consistency
Parameter logCons : exists(A : Ty), Tm A -> False.
 *)

(* System T is a total language, we don't prove this (we would need to
do induction on the syntax of System T) *)
Parameter canonicityNat : forall(t : Tm Nat), exists n, t = quote n.

(* let's write/specify a "nat -> nat -> nat" function which is not definable in System T *)
(* TODO: is this even definable in the presheaf semantics? *)
Parameter (code : Tm (Nat ⇒ Nat) -> nat).
Parameter (eval : nat -> nat -> nat).
Parameter (evalProp : forall(u : Tm (Nat ⇒ Nat))(n : nat),
  quote (eval (code u) n) = u ⋅ quote n).
Parameter (nontrivial : forall t, ~ t = suc t).

Goal ~ definable2 eval.
Proof.
  unfold not. intros. unfold definable2, defines2 in H.
  destruct H as [t H].
  pose (u := lam (fun x => suc (t ⋅ x ⋅ x))).
  specialize (H (code u) (code u)).
  rewrite evalProp in H.
  subst u.
  rewrite arrβ in H.
  apply nontrivial in H.
  exact H.
(*

t ⋅ quote (code u) ⋅ quote (code u)
                                           =(eval is definable)
quote (eval (code u) (code u))
                                           =(evalProp)
u ⋅ quote (code u)
                                           =(definition of u)
suc (t ⋅ quote (code u) ⋅ quote (code u))

*)
Qed.

End SystemT_with_ite.

Module SystemT.

Parameter (Ty : Type).
Parameter (Tm : Ty -> Type).

Parameter arr  : Ty -> Ty -> Ty.
Notation "x ⇒ y" := (arr x y) (at level 80, right associativity).
Parameter app  : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y" := (app x y) (at level 50, left associativity).
Parameter lam  : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 51, x name).
Parameter arrβ : forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a.
Parameter arrη : forall {A B : Ty} (f : Tm (A ⇒ B)), f = λ x, f ⋅ x.

Parameter (Nat : Ty).
Parameter (zero   : Tm Nat).
Parameter (suc    : Tm Nat -> Tm Nat).
(* recursor for Nat *) (*                !!!!!!               *)
Parameter (rec    : forall {A}, Tm A -> (Tm Nat -> Tm A -> Tm A) -> Tm Nat -> Tm A).
Parameter (Natβ₁  : forall {A z s},   @rec A z s zero = z).
Parameter (Natβ₂  : forall {A z s u}, @rec A z s (suc u) = s u (rec z s u)).

Definition one   : Tm Nat := suc zero.
Definition two   : Tm Nat := suc one.
Definition three : Tm Nat := suc two.
Definition four  : Tm Nat := suc three.
Definition seven : Tm Nat := suc (suc (suc four)).

Definition pred : Tm (Nat ⇒ Nat). Admitted.
Goal pred ⋅ zero = zero.
Proof.
Admitted.
Goal forall u, pred ⋅ (suc u) = u.
Proof.
Admitted.

Fixpoint quote (n : nat) : Tm Nat :=
  match n with
  | O => zero
  | S n => suc (quote n)
  end.

Goal forall n, pred ⋅ (suc (quote n)) = quote n.
Proof.
Admitted.

(* testing equality using C-style Bool *)
Definition Bool  : Ty. Admitted.
Definition false : Tm Bool. Admitted.
Definition true  : Tm Bool. Admitted.
Definition ite {A : Ty} (b : Tm Bool) (u v : Tm A) : Tm A. Admitted.
Goal forall A (u v : Tm A), ite true u v = u.
Proof.
Admitted.
Goal forall A (u v : Tm A), ite false u v = v.
Proof.
Admitted.

Definition isZero : Tm (Nat ⇒ Bool). Admitted.
Goal isZero ⋅ zero = true.
Proof.
Admitted.
Goal isZero ⋅ one = false.
Proof.
Admitted.
Goal isZero ⋅ two = false.
Proof.
Admitted.

Definition eq : Tm (Nat ⇒ Nat ⇒ Bool). Admitted.
Goal eq ⋅ zero ⋅ zero = true.
Proof.
Admitted.
Goal eq ⋅ one ⋅ one = true.
Proof.
Admitted.
Goal eq ⋅ two ⋅ two = true.
Proof.
Admitted.
Goal eq ⋅ one ⋅ two = false.
Proof.
Admitted.
Goal eq ⋅ two ⋅ one = false.
Proof.
Admitted.

(* a nyelvunk trivialis, ha zero = suc zero. *)
Goal zero = suc zero -> forall A (u v : Tm A), u = v.
Proof.
Admitted.

(* a nyelvunk trivialis, ha van olyan t, hogy t = suc t. *)
Goal (exists t, t = suc t) -> forall A (u v : Tm A), u = v.
Proof.
Admitted.

End SystemT.

