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

Module SystemTrec.

(* recursor for Nat *)
Parameter (rec   : forall {A}, Tm A -> (Tm Nat -> Tm A -> Tm A) -> Tm Nat -> Tm A).
Parameter (Natβ₁ : forall {A z s},   @rec A z s zero = z).
Parameter (Natβ₂ : forall {A z s u}, @rec A z s (suc u) = s u (rec z s u)).

Definition coqpred (n : nat) : nat :=
match n with
| O => O
| S m => m
end.

Compute coqpred 0.
Compute coqpred 2.

Definition pred : Tm (Nat ⇒ Nat) := λ n, rec zero (fun x y => x) n.
Goal pred ⋅ zero = zero.
Proof.
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₁.
  reflexivity.
Qed.

Goal pred ⋅ two = one.
Proof.
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₂.
  reflexivity.
Qed.

Goal forall u, pred ⋅ (suc u) = u.
Proof.
  cbv.
  intros.
  rewrite ! arrβ.
  rewrite Natβ₂.
  reflexivity.
Qed.

(* n   = suc (suc (suc zero)) *)
(* m  = suc (suc zero) *)
(* n - m = suc zero *)

Definition minus : Tm (Nat ⇒ Nat ⇒ Nat) := lam (fun n => lam (fun m => rec n (fun _ y => pred ⋅ y) m)).
Goal minus ⋅ seven ⋅ three = four.
Proof.
  cbv.
  rewrite ! arrβ.
  rewrite ! Natβ₂.
  rewrite ! Natβ₁.
  rewrite ! arrβ.
  rewrite ! Natβ₂.
  reflexivity.
Qed.
Goal minus ⋅ two ⋅ three = zero.
Proof.
  cbv.
  rewrite ! arrβ.
  rewrite ! Natβ₂.
  rewrite ! Natβ₁.
  rewrite ! arrβ.
  rewrite ! Natβ₂.
  rewrite Natβ₁.
  reflexivity.
Qed.

End SystemTrec.

Module SystemTite.

(* iteration on Nat *)
Parameter (iter  : forall {A}, Tm A -> (Tm A -> Tm A) -> Tm Nat -> Tm A).
Parameter (Natβ₁ : forall {A z s},   @iter A z s zero = z).
Parameter (Natβ₂ : forall {A z s u}, @iter A z s (suc u) = s (iter z s u)).

(* defining C-style Bool via Nat *)
Definition Bool  : Ty := Nat.
Definition false : Tm Bool := zero.
Definition true  : Tm Bool := one.
Definition ite {A : Ty} (b : Tm Bool) (u v : Tm A) : Tm A := iter v (fun _ => u) b.
Lemma iteβ₁ : forall A (u v : Tm A), ite true u v = u.
Proof.
  intros.
  cbv.
  rewrite Natβ₂.
  reflexivity.
Qed.
Lemma iteβ₂ : forall A (u v : Tm A), ite false u v = v.
Proof.
  intros.
  cbv.
  rewrite Natβ₁.
  reflexivity.
Qed.

Definition isZero : Tm (Nat ⇒ Bool) := λ n, ite n false true .
Goal isZero ⋅ zero = true.
Proof.
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₁.
  reflexivity.
Qed.
Goal isZero ⋅ one = false.
Proof.
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₂.
  reflexivity.
Qed.
Goal isZero ⋅ two = false.
Proof.
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₂.
  reflexivity.
Qed.

Definition Prod : Ty -> Ty := fun A => Bool ⇒ A.
Definition pair : forall {A}, Tm A -> Tm A -> Tm (Prod A) := fun _ x y => λ b, ite b x y.
Definition fst  : forall {A}, Tm (Prod A) -> Tm A := fun _ p => p ⋅ true.
Definition snd  : forall {A}, Tm (Prod A) -> Tm A := fun _ p => p ⋅ false.
Lemma Prodβ₁ : forall {A} {a a' : Tm A}, fst (pair a a') = a.
Proof.
  intros.
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₂.
  reflexivity.
Qed.
Lemma Prodβ₂ : forall {A} {a a' : Tm A}, snd (pair a a') = a'.
Proof.
  intros.
  cbv.
  rewrite ! arrβ.
  rewrite Natβ₁.
  reflexivity.
Qed.
(* this is not provable *) 
(* Definition Prodη : w = pair (fst w) (snd w). *)

Definition pred (t : Tm Nat) : Tm Nat := fst (iter (pair zero zero) (fun p => (pair (snd p) (suc (snd p)))) t).
Goal pred (suc two) = two.
Proof.
  cbv.
  rewrite ! Natβ₂.
  rewrite ! arrβ.
  rewrite ! Natβ₁.
  rewrite ! Natβ₂.
  rewrite ! arrβ.
  rewrite ! Natβ₁.
  reflexivity.
  Restart.
  cbv.
  now repeat rewrite ? arrβ, ? Natβ₂, ? Natβ₁.
Qed.
Goal pred (suc three) = three.
Proof.
    cbv.
    now repeat rewrite ? arrβ, ? Natβ₂, ? Natβ₁.
Qed.
Lemma predsuc : forall n, pred (suc (quote n)) = quote n.
Proof.
  intros.
  cbv -[quote].
  repeat rewrite ? arrβ, ? Natβ₂, ? Natβ₁.
  induction n ; simpl.
  now rewrite Natβ₁, arrβ, Natβ₁.
  rewrite Natβ₂, arrβ, Natβ₁.
  remember (iter _ _ _ ⋅ _).
  rewrite IHn.
  reflexivity.
Qed.

(* the language is trivial if zero = suc zero. *)
Lemma zsztriv : zero = suc zero -> forall A (u v : Tm A), u = v.
Proof.
  intros.
  apply (f_equal (fun x => ite x u v)) in H.
  cbv in H. rewrite Natβ₁, Natβ₂ in H.
  symmetry.
  exact H.
(*   apply (f_equal (fun x => isZero ⋅ x)) in H.
  cbv in H. rewrite ? arrβ, Natβ₁, Natβ₁ in H. *)
Qed.

Goal (exists n, quote n = suc (quote n)) -> forall A (u v : Tm A), u = v.
Proof.
Admitted.

(* we can define the recursor from the iterator if we have
heterogeneous pairs, however we cannot prove its computation rules *)
(* Definition rec (A : Ty)(z : Tm A)(s : Tm Nat -> Tm A -> Tm A)(n : Tm Nat) : Tm A
  := snd (@ite (Pair Nat A) (pair zero z) (fun w => pair (suc (fst w) (s (fst w) (snd w)))) n).
*)

(*
we need the recursor to define this easily (it is still not very easy)
Definition eq : Tm (Nat ⇒ Nat ⇒ Bool). Admitted.
Goal eq ⋅ zero ⋅ zero = true. Admitted.
Goal eq ⋅ one ⋅ one = true. Admitted.
Goal eq ⋅ two ⋅ two = true. Admitted.
Goal eq ⋅ one ⋅ two = false. Admitted.
Goal eq ⋅ two ⋅ one = false. Admitted.
*)

End SystemTite.

Module U.

(* well-scoped De Bruijn indices: *)
Inductive Var : nat -> Type :=
  | vz : forall {n}, Var (S n)
  | vs : forall {n}, Var n -> Var (S n)
.

(* well-scoped terms (ABTs) *)
Inductive Tm : nat -> Type :=
  | var    : forall {n}, Var n -> Tm n
  | ann    : forall {n}, Tm n -> Ty -> Tm n
  | app    : forall {n}, Tm n -> Tm n -> Tm n
  | lam    : forall {n}, Tm (S n) -> Tm n
  | zero   : forall {n}, Tm n
  | suc    : forall {n}, Tm n -> Tm n
  | iter   : forall {n}, Tm n -> Tm n -> Tm n -> Tm n
.

End U.

Module TypecheckingSystemTiter.

Parameter (iter  : forall {A}, Tm A -> (Tm A -> Tm A) -> Tm Nat -> Tm A).
Parameter (Natβ₁ : forall {A z s},   @iter A z s zero = z).
Parameter (Natβ₂ : forall {A z s u}, @iter A z s (suc u) = s (iter z s u)).

Definition eqTy (A B : Ty) : {A = B} + {A <> B}.
Proof.
  decide equality.
Defined.

Fixpoint Con (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => Con n * Ty
  end.

Fixpoint El {n : nat} : Con n -> Type :=
  match n with
  | 0 => fun Γ => unit
  | S n => fun Γ => (El (fst Γ) * Tm (snd Γ))%type
  end.

Fixpoint lookup {n} (x : U.Var n) : forall Γ : Con n, {A : Ty & El Γ -> Tm A} :=
  match x with
  | U.vz => fun Γ => existT _ (snd Γ) snd
  | U.vs y => fun Γ =>
      match lookup y (fst Γ) with
      | existT _ A f => existT _ A (fun el => f (fst el))
      end
  end.

Fixpoint infer {n} (t : U.Tm n) : forall Γ : Con n, option {A : Ty & El Γ -> Tm A} :=
  match t with
  | U.var x => fun Γ => Some (lookup x Γ)
  | U.ann t A => fun Γ =>
      match check t A Γ with
      | Some f => Some (existT _ A f)
      | None => None
      end
  | U.zero => fun Γ => Some (existT _ Nat (fun _ => zero))
  | U.suc t => fun Γ =>
      match check t Nat Γ with
      | Some f => Some (existT _ Nat (fun el => suc (f el)))
      | None => None
      end
  | U.iter z s n => fun Γ =>
      match infer z Γ with
      | Some (existT _ A fz) =>
          match check s (A ⇒ A) Γ, check n Nat Γ with
          | Some fs, Some fn =>
              Some (existT _ A (fun el => iter (fz el) (app (fs el)) (fn el)))
          | _, _ => None
          end
      | _ => None
      end
  | U.app t u => fun Γ =>
      match infer t Γ with
      | Some (existT _ (A ⇒ B) ft) =>
          match check u A Γ with
          | Some fu => Some (existT _ B (fun el => app (ft el) (fu el)))
          | None => None
          end
      | _ => None
      end
  | U.lam t => fun Γ => None
  end
with check {n} (t : U.Tm n) (T : Ty) : forall Γ : Con n, option (El Γ -> Tm T) :=
  match t with
  | U.lam t => fun Γ =>
      match T with
      | A ⇒ B =>
          match check t B (Γ, A) with
          | Some f => Some (fun el => lam (fun x => f (el, x)))
          | None => None
          end
      | _ => None
    end
  | U.app t u => fun Γ =>
      match infer u Γ with
      | Some (existT _ A fu) =>
          match check t (A ⇒ T) Γ with
          | Some ft => Some (fun el => app (ft el) (fu el))
          | None => None
          end
      | None => None
      end
  | U.var x => fun Γ =>
      match lookup x Γ with
      | existT _ A f =>
          match eqTy A T with
          | left E => match E with eq_refl => Some f end
          | _ => None
          end
      end
  | U.ann t A => fun Γ =>
      match eqTy A T with
      | left E => check t T Γ
      | _ => None
      end
  | U.zero => fun Γ =>
      match eqTy Nat T with
      | left E => match E with eq_refl => Some (fun _ => zero) end
      | _ => None
      end
  | U.suc t => fun Γ =>
      match eqTy Nat T, check t Nat Γ with
      | left E, Some f => match E with eq_refl =>
                            Some (fun el => suc (f el))
                          end
      | _, _ => None
      end
  | U.iter z s n => fun Γ =>
      match check z T Γ, check s (T ⇒ T) Γ, check n Nat Γ with
      | Some fz, Some fs, Some fn =>
          Some (fun el => iter (fz el) (fun x => app (fs el) x) (fn el))
      | _, _, _ => None
      end
  end.

Definition infer_closed (t : U.Tm 0) : option {A : Ty & Tm A} :=
  match infer t tt with
  | Some (existT _ A f) => Some (existT _ A (f tt))
  | None => None
  end.

Compute infer_closed (U.lam (U.var U.vz)).
Compute infer_closed (U.ann (U.lam (U.var U.vz)) (Nat ⇒ Nat)).
Compute infer_closed (U.ann (U.lam (U.var U.vz)) ((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat))).
Compute infer_closed (U.ann (U.lam (U.var U.vz)) (Nat ⇒ (Nat ⇒ Nat))).
Compute infer_closed (U.ann (U.app (U.lam (U.var U.vz)) U.zero) Nat).
Compute infer_closed (U.ann (U.app (U.lam (U.var U.vz)) U.zero) Nat).

(* Our basic inference heuristics sometimes fail: *)

Definition id n := @U.lam n (U.var U.vz).
Definition u := U.app (U.ann (id 0) (Nat ⇒ Nat)) (U.app (id 0) U.zero).

Goal exists A t, infer_closed u = Some (existT _ A t).
Proof.
  compute. exists Nat.
  exists (lam (fun x => x) ⋅ (lam (fun x => x) ⋅ zero)).
  reflexivity.
Qed.

Goal infer_closed (U.ann u Nat) = None.
Proof. reflexivity. Qed.

(* Can you explain what is going on? Why does adding a
   correct type annotation make type inference fail?
   Difficult homework for motivated students: improve
   the function so that this doesn't happen. Bonus: prove
   that it doesn't happen! *)

Definition t := (lam (fun n => iter (suc zero) (fun x => lam suc ⋅ x) n)).
Goal exists u, infer_closed u = Some (existT _ (Nat ⇒ Nat) t).
Proof.
  exists (U.ann
    (@U.lam 0 (U.iter (U.suc U.zero) (U.lam (U.suc (U.var U.vz))) (U.var U.vz)))
    (Nat ⇒ Nat)).
  reflexivity.
Qed.

Definition s (A B C : Ty) :=
  U.ann (@U.lam 0 (U.lam (U.lam (U.app
      (U.app (U.var (U.vs (U.vs U.vz))) (U.var U.vz))
      (U.app (U.var (U.vs U.vz)) (U.var U.vz))))))
    ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C).

Definition S (A B C : Ty) :=
  lam (fun (x : Tm (A ⇒ B ⇒ C)) =>
         lam (fun (y : Tm (A ⇒ B)) =>
                lam (fun (z : Tm A) =>
                       (x ⋅ z) ⋅ (y ⋅ z)))).

Lemma eqTyRefl (A : Ty) : eqTy A A = left eq_refl.
Proof.
  induction A as [|A1 IH1 A2 IH2].
  - reflexivity.
  - simpl. rewrite IH1, IH2. compute. reflexivity.
Qed.

Goal forall A B C : Ty, infer_closed (s A B C) = Some (existT _ _ (S A B C)).
Proof.
  intros A B C.
  (* Opaque eqTy. *)
  compute. repeat rewrite eqTyRefl. reflexivity.
Qed.

End TypecheckingSystemTiter.
