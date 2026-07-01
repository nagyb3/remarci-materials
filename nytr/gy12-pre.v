Require Import Setoid.

(* System F *)
Parameter Ty         : Type.
Parameter Tm         : Ty -> Type.

Parameter arr        : Ty -> Ty -> Ty.
Notation "A ⇒ B"     := (arr A B) (at level 80, right associativity).
Parameter app        : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y"     := (app x y) (at level 50, left associativity).
Parameter lam        : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 81, x name).
Parameter arrβ       : forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a.
Parameter arrη       : forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun a => f ⋅ a).

Parameter Forall     : (Ty -> Ty) -> Ty.
Notation "∀ F"       := (Forall F) (at level 80). (* \forall *)
Notation "∀λ A , F"  := (Forall (fun A => F)) (at level 81, A name). (* \forall *)
Parameter Lam        : forall {F : Ty -> Ty}, (forall (X : Ty), Tm (F X)) -> Tm (∀ F).
Notation "'Λ' x , f" := (Lam (fun x => f)) (at level 81, x name).
Parameter App        : forall {F : Ty -> Ty}, Tm (∀ F) -> forall (X : Ty), Tm (F X).
Notation "t • X"     := (App t X) (at level 50, left associativity). (* \bullet *)
Parameter Forallβ    : forall {F : Ty -> Ty} {t : forall (X : Ty), Tm (F X)} {X : Ty}, App (Lam t) X = t X.
Parameter Forallη    : forall {F : Ty -> Ty} (f : Tm (∀ F)), f = Lam (fun X => f • X).

(*
   Tm (∀ F) ≅ (forall (A : Ty), Tm (F A))
   ∀ F = F A₀ × F A₁ × F A₂ × F A₃ × ...   (for every type A₀,...)

   Not quite a fixpoint:
   (∀ F)   <-/-> F (∀ F)
   ∀(λX.X) = ⊥ = (λX.X) (∀(λX.X))
   ∀(λX.X⇒X) = ⊤ = ⊤⇒⊤ = (λX.X⇒X) (∀(λX.X⇒X))
   ∀(λX.X⇒X⇒X) = Bool ≠ Bool⇒Bool⇒Bool = (λX.X⇒X⇒X) (∀(λX.X⇒X⇒X))
 *)
                                     

(* 1. polymorphism *)

(* In Haskell:

   id :: a -> a <- implicit ∀
   -- id :: forall a. a -> a
   id x = x
*)

(* until now, only definable using a "macro" that generates id functions: *)
Definition id'' (A : Ty) : Tm (A ⇒ A) := lam id.

(* now definable as one polymorphic function *)
Definition id' : Tm (∀λ A, A ⇒ A) := Lam id''.
(* Definition id : Tm (∀ (fun A => A ⇒ A)) := Lam (fun A => lam (fun a => a)). *)

Lemma id'_is_id : forall A (x : Tm A), id' • A ⋅ x = x.
Proof.
  intros.
  cbv.
  rewrite Forallβ, arrβ.
  reflexivity.
Defined.

(* In Haskell

   comp :: (b -> c) -> (a -> b) -> (a -> c) <- implicit ∀
   comp g f x = g (f x)
*)

Definition comp : Tm (∀λ A, ∀λ B, ∀λ C, (B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) :=
  Λ A, Λ B, Λ C, λ g, λ f, λ x, g ⋅ (f ⋅ x).

Goal forall A B C g f x, comp • A • B • C ⋅ g ⋅ f ⋅ x = g ⋅ (f ⋅ x).
Proof.
  Locate "->".
  refine (fun A V C g f x => _).

  Restart.

  intros.
  cbv.
  rewrite ! Forallβ.
  rewrite ! arrβ.
  reflexivity.
Qed.

(* In Haskell:

   flip :: (a -> b -> c) -> (b -> a -> c) <- implicit ∀
   flip f a b = f b a
*)

Definition flip : Tm (∀λ A, ∀λ B, ∀λ C, (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C). Admitted.



(*
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
ZH-N ILYESMI VÁRHATÓ (meg Nat egyszeru megadása?)
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
*)
(* 2. encoding inductive types using ∀ *)

(* System F can express (co)inductive types with Church encoding: *)
Definition Bool := ∀λ A, A ⇒ A ⇒ A.

Definition true  : Tm Bool := Λ A, λ t, λ f, t.
Definition false : Tm Bool := Λ A, λ t, λ f, f.

Definition iteBool : forall {A} (t f : Tm A) (b : Tm Bool), Tm A :=
  fun A t f b => b • A ⋅ t ⋅ f.

Lemma Boolβ₁ : forall {A} (t f : Tm A), iteBool t f true = t.
Proof.
  intros. cbv.
  now rewrite Forallβ, ! arrβ.
Qed.

Lemma Boolβ₂ : forall {A} (t f : Tm A), iteBool t f false = f.
Proof.
  intros. cbv.
  now rewrite Forallβ, ! arrβ.
Qed.

(*
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
ZH-N ILYESMI VÁRHATÓ (meg Nat egyszeru megadása?)
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
*)


(* 
(* Eta-rules are not provable :( *) *)

(* iteUnit : forall {A} (t : Tm A) (u : Tm Unit), Tm A := t *)
Definition Unit : Ty := ∀λ A, A ⇒ A.
Definition tt : Tm Unit := id'.

Definition Empty : Ty := ∀λ A, A.
Definition exfalso : forall {A} (e : Tm Empty), Tm A. Admitted.

Definition Prod (A B : Ty) : Ty := ∀λ X, (A ⇒ B ⇒ X) ⇒ X.
Notation "A × B" := (Prod A B) (at level 78, right associativity). (* \times *)

Definition pair {A B} (a : Tm A) (b : Tm B) : Tm (A × B) := Λ X, λ f, f ⋅ a ⋅ b.
Notation "x , y"  := (pair x y) (at level 80, right associativity).

Definition fst {A B} (p : Tm (A × B)) : Tm A. Admitted.
Definition snd {A B} (p : Tm (A × B)) : Tm B. Admitted.

Lemma Prodβ₁ : forall {A B} (a : Tm A) (b : Tm B), fst (a , b) = a.
Proof.
Admitted.

Lemma Prodβ₂ : forall {A B} (a : Tm A) (b : Tm B), snd (a , b) = b.
Proof.
Admitted.

(* idea: for any algebra, I get an element of the carrier *)
Definition Nat : Ty := ∀λ A, A ⇒ (A ⇒ A) ⇒ A.

Definition zero : Tm Nat := Λ A, λ z, λ s, z.
Definition suc (n : Tm Nat) : Tm Nat := Λ A, λ z, λ s, s ⋅ (n • A ⋅ z ⋅ s).
Definition iteNat : forall {A}, Tm A -> (Tm A -> Tm A) -> Tm Nat -> Tm A := fun A z s n => n • A ⋅ z ⋅ lam s.

Lemma Natβ₁ : forall {A} (z : Tm A) (s : Tm A -> Tm A), iteNat z s zero = z.
Proof.
  intros.
  cbv.
  rewrite Forallβ, ! arrβ.
  reflexivity.
Defined.

Lemma Natβ₂ : forall {A} (z : Tm A) (s : Tm A -> Tm A) (n : Tm Nat), iteNat z s (suc n) = s (iteNat z s n).
Proof.
  intros.
  cbv.
  rewrite ! Forallβ.
  rewrite ! arrβ.
  reflexivity.
Defined.

Definition List (A : Ty) : Ty. Admitted.

Definition nil {A} : Tm (List A). Admitted.
Definition cons {A} (x : Tm A) (xs : Tm (List A)) : Tm (List A). Admitted.

Definition iteList {A B : Ty} (z : Tm B) (s : Tm A -> Tm B -> Tm B) (xs : Tm (List A)) : Tm B. Admitted.

Lemma iteListβ₁ : forall {A B : Ty} (z : Tm B) (s : Tm A -> Tm B -> Tm B), iteList z s nil = z.
Proof.
Admitted.

Lemma iteListβ₂ : forall {A B : Ty} (z : Tm B) (s : Tm A -> Tm B -> Tm B) (x : Tm A) (xs : Tm (List A)),
  iteList z s (cons x xs) = s x (iteList z s xs).
Proof.
Admitted.

Definition isNil {A} (xs : Tm (List A)) : Tm Bool. Admitted.

Definition head {A} (xs : Tm (List A)) (err : Tm A) : Tm A. Admitted.

Definition tail {A} (xs : Tm (List A)) : Tm (List A). Admitted.

(* HW: encode binary trees *)
Definition Tree : Ty := ∀λ X, X ⇒ (X ⇒ X ⇒ X) ⇒ X.


(* 3. abstraction *)

(* functions defined on an interface of stacks, implementation-independent

   the interface:
     S       : Ty
     empty   : Tm S
     push    : Tm (S ⇒ Nat ⇒ S)
     top     : Tm (S ⇒ Nat)
     pop     : Tm (S ⇒ S)
     isEmpty : Tm (S ⇒ Bool)
 *)

Module StackMeta.

  Require Import List Datatypes.

  Class NatStack := {
    S : Type;
    empty : S;
    push : S -> nat -> S;
    top : S -> nat;
    pop : S -> S;
    isEmpty : S -> bool;
    (* transform : S -> (S -> S) -> S *)
  }.

  (* Not quite a coinductive type:
     - can't define empty
     - needs strict positivity

     CoInductive NatStack := {
       empty : ???;
       push : nat -> NatStack;
       top : nat;
       pop : NatStack;
       isEmpty : bool;
       transform : (NatStack -> NatStack) -> NatStack (* fails *)
     }.
   *)

  Definition aStack (ns : NatStack) : S := pop (push (push empty 1) 2).

  Instance listStack : NatStack := {|
    S := list nat;
    empty := nil;
    push xs x := cons x xs;
    top xs := hd 0 xs;
    pop xs := tl xs;
    isEmpty xs := if xs then true else false
  |}.

  Goal aStack listStack = cons 1 nil.
  Proof. reflexivity. Qed.

End StackMeta.

Module BlindCopy.

  Definition NatStack := (fun S => S × (S ⇒ Nat ⇒ S) × (S ⇒ Nat) × (S ⇒ S) × (S ⇒ Bool)).

  Definition aStack : Tm (∀ (fun S => NatStack S ⇒ S)) :=
    Λ S, λ stack, 
    let empty := fst stack in
    let push := fst (snd stack) in
    let top := fst (snd (snd stack)) in
    let pop := fst (snd (snd (snd stack))) in
    let isEmpty := snd (snd (snd (snd stack))) in
    pop ⋅ (push ⋅ (push ⋅ empty ⋅ suc zero) ⋅ (suc (suc zero)))
  .

  Definition listStack : Tm (NatStack (List Nat)) := (
    nil,
    (λ xs, λ x, cons x xs),
    (λ xs, head xs zero),
    lam tail,
    lam isNil
  ).

  Goal aStack • (List Nat) ⋅ listStack = cons (suc zero) nil.
  Proof.
  Admitted.

End BlindCopy.

Module InPlace.

  Definition aStack : Tm (∀ (fun S => S ⇒ (S ⇒ Nat ⇒ S) ⇒ (S ⇒ Nat) ⇒ (S ⇒ S) ⇒ (S ⇒ Bool) ⇒ S)) :=
    Λ S, λ empty, λ push, λ top, λ pop, λ isEmpty,
    pop ⋅ (push ⋅ (push ⋅ empty ⋅ suc zero) ⋅ (suc (suc zero)))
  .

  Goal aStack • List Nat
              ⋅ nil
              ⋅ (λ xs, λ x, cons x xs)
              ⋅ (λ xs, head xs zero)
              ⋅ (lam tail)
              ⋅ (lam isNil)
    = cons (suc zero) nil.
  Proof.
  Admitted.

End InPlace.


(* 4. coinductive types *)

(* FOL: ∃ P(x) <=> ¬∀ (¬P(x)) *)
Definition Exists : (Ty -> Ty) -> Ty := fun F => ∀λ C, (∀λ X, F X ⇒ C) ⇒ C.

(* ∃ F = F A₀ ⊎ F A₁ ⊎ F A₂ ⊎ F A₃ ⊎ ...   (for every type A₀,...)  *)
                                                   
Notation "∃ F"      := (Exists F) (at level 80).
Notation "∃λ A , F" := (Exists (fun A => F)) (at level 81, A name).
Definition mkExists : forall {F : Ty -> Ty} (X : Ty), Tm (F X) -> Tm (∃ F) := fun F X w => Λ C, λ u, u • X ⋅ w.
Definition case     : forall {F : Ty -> Ty} {C : Ty}, (forall (X : Ty), Tm (F X) -> Tm C) -> Tm (∃ F) -> Tm C :=
  fun F C t w => w • C ⋅ Λ X, λ u, t X u.
Definition Existsβ  : forall {F : Ty -> Ty} {C : Ty} (t : forall (X : Ty), Tm (F X) -> Tm C) (X : Ty) (w : Tm (F X)),
  case t (mkExists X w) = t X w.
Proof.
  intros. cbv. now repeat rewrite ? Forallβ, ? arrβ.
Qed.

Module Stream.

  Definition Stream (A : Ty) : Ty := ∃λ X, (X ⇒ A) × (X ⇒ X) × X.

  Definition head      : forall {A}, Tm (Stream A) -> Tm A. Admitted.
  Definition tail      : forall {A}, Tm (Stream A) -> Tm (Stream A). Admitted.
  Definition genStream : forall {A C}, (Tm C -> Tm A) -> (Tm C -> Tm C) -> Tm C -> Tm (Stream A). Admitted.

  Lemma Streamβ₁  : forall {A C} (h : Tm C -> Tm A) (t : Tm C -> Tm C) (c : Tm C),
    head (genStream h t c) = h c.
  Proof.
  Admitted.
  Definition Streamβ₂  : forall {A C} (h : Tm C -> Tm A) (t : Tm C -> Tm C) (c : Tm C),
    tail (genStream h t c) = genStream h t (t c).
  Proof.
  Admitted.

End Stream.

(* HW: Church encode more coinductive types *)

(*
   F X = A × X
   (C → A × C) → C → (∃ X. (X ---> A × X) × X)
   (A×C→C) → (∀ X. (A × X --> X) ---> X) ---> C
 *)
