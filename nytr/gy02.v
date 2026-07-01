(**
  Type systems (Nyelvek típusrendszere) tutorial (gyakorlat)
*)

Require Import Nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Arith.

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Program.Basics.

Local Open Scope char_scope.
Open Scope string_scope.
Open Scope list_scope.
Local Open Scope program_scope.

Definition bind {A B : Type}(oa : option A)(f : A -> option B) : option B :=
  match oa with
  | Some a => f a
  | None => None
  end.

(************************************************************
 abstraction level 1: a program is a string
*************************************************************

"num 3 - num 2" does not make sense because we don't have subtraction

"isZero (num 1)"   ≠   "isZero     (num 1)"

 *)

(************************************************************
 abstraction level 2: a program is a list of lexical elements
*************************************************************

Lexical elements: (, ), true, false, if, then, else, num, isZero, +, 0, 1, 2, ...

Now both "isZero (num 1)" and "isZero     (num 1)" are the same lists [isZero, (, num, 1, )].

But: [(, true] does not make sense (closing bracket is missing).

[(, true, )]  ≠  [true]

 *)

Module L.

Inductive Lex : Type := Open | Close | true | false | if' | then' | else' | num (n : nat) | isZero | plus.

Goal ~ (Open :: true :: Close :: nil = true :: nil). discriminate. Qed.

(* you can fix this *)
Definition to_string (n : nat) : string := "NUM".

(* a very stupid printing function *)
Fixpoint print (ls : list Lex) : string :=
  match ls with
  | nil => ""
  | Open   :: ls => "(" ++ print ls
  | Close  :: ls => ")" ++ print ls
  | true   :: ls => "true " ++ print ls
  | false  :: ls => "false " ++ print ls
  | if'    :: ls => "if " ++ print ls
  | then'  :: ls => "then " ++ print ls
  | else'  :: ls => "else " ++ print ls
  | num n  :: ls => "num " ++ to_string n ++ " " ++ print ls
  | isZero :: ls => "isZero " ++ print ls
  | plus   :: ls => "+" ++ print ls
  end.

Compute (print (Open :: true :: Close :: nil)).

(* optional homework: write a lexer *)

End L.

(************************************************************
 abstraction level 3: a program is an abstract syntax tree
*************************************************************)

Module U.

(* these are the programs: *)
Inductive Tm : Type :=
| true   : Tm
| false  : Tm
| ite    : Tm -> Tm -> Tm -> Tm
| num    : nat -> Tm
| isZero : Tm -> Tm
| plus   : Tm -> Tm -> Tm.

Notation "x + y" := (plus x y) (at level 50, left associativity).

Definition notMeaningful : Tm := isZero true.

(*
we can only define a C-style evaluator (meaning, denotational semantics, interpreter)
of the AST where booleans and integers are merged
 *)

Fixpoint eval (t : Tm) : nat :=
  match t with
  | true => 1
  | false => 0
  | ite t u v => match (eval t) with
                 | 0 => eval v
                 | _ => eval u
                 end
  | _ => 0 (* remove this line *)
  end.

Example notEq : exists t1 t2 : Tm, ~ t1 = t2 /\ eval t1 = eval t2.
exists false. exists (num 0). split.
- intro. discriminate H.
- simpl. reflexivity.
Qed.

Close Scope string_scope.

Fixpoint toLex (t : Tm) : list L.Lex :=
  match t with
  | true => L.true :: nil
  | false => L.false :: nil
                 (* x   :: [y, z, w] ++  f :: ... *)
  | ite t u v => L.if' :: (toLex t ++ (L.then' :: toLex u ++ L.else' :: toLex v)) (* maybe we need some brackets here? *)
  | num n => L.num n :: nil
  | isZero t => L.isZero :: L.Open :: toLex t ++ (L.Close :: nil)
  | plus t u => toLex t ++ L.plus :: toLex u
  end.

Goal toLex true = L.true :: nil. reflexivity. Qed.

(* optional homework: write a parser, show its correctness: parse ∘ toLex = id *)

End U.

(************************************************************
 abstraction level 4: a program is a well-typed syntax tree
*************************************************************)

Module Typed.

Definition true' : bool := true.
Definition false' : bool := false.

Inductive Ty : Type := Bool | Nat.

Inductive Tm : Ty -> Type :=
| true   : Tm Bool
| false  : Tm Bool
| ite    : forall{A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A
| num    : nat -> Tm Nat
| isZero : Tm Nat -> Tm Bool
| plus   : Tm Nat -> Tm Nat -> Tm Nat.

Notation "x + y" := (plus x y) (at level 50, left associativity).

(* ite has an implicit argument: *)
Check ite true (num 1) (num 2).
Check @ite Nat true (num 1) (num 2).
Check @ite _ true (num 1) (num 1).
Fail Check @ite Bool true (num 1) (num 2).
Fail Check ite true (num 1) false.

(**
  Type erasure: from typed to untyped
*)
Reserved Notation "⟦ a ⟧".
Fixpoint erase {A : Ty}(a : Tm A) : U.Tm :=
  match a with
  | true => U.true
  | false => U.false
  | ite t u v => U.ite ⟦ t ⟧ ⟦ u ⟧ ⟦ v ⟧
  | num n => U.num n
  | isZero t => U.isZero ⟦ t ⟧
  | plus u v => (U.plus ⟦ u ⟧ ⟦ v ⟧)
  end
where "⟦ a ⟧" := (erase a).
(*
  \lobrk = ⟦
  \robrk = ⟧
*)

Goal exists (A : Ty)(a : Tm A), ⟦ a ⟧ = U.isZero (U.num 2).
Proof.
  exists Bool. exists (isZero (num 2)). simpl. reflexivity.
Qed.

Goal exists (A : Ty)(a : Tm A), ⟦ a ⟧ = U.ite (U.isZero (U.plus (U.num 0) (U.num 1))) U.false (U.isZero (U.num 0)).
Proof.
  exists Bool.
  exists (ite (isZero (num 0 + num 1)) false (isZero (num 0))).
  simpl. reflexivity.
Qed.

(* EXE *)
Goal exists (A : Ty)(a : Tm A), ⟦ a ⟧ = U.ite U.true U.true U.true.
Proof.
  exists Bool.
  exists (ite true true true).
  simpl. reflexivity.
Qed.

(**
  Think about it: is there an untyped expression which cannot be the result of type erasure?

  Examples:

  U.ite U.true (U.num 1) U.false
  U.ite (U.num 1) U.true U.true
  U.isZero U.true
*)

Goal ~ exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.isZero (U.true). 
Proof.
  Locate "~".
  Print not.
  unfold not.
  intros.
  destruct H. destruct H.
  destruct x0.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H.
  remember Nat.
  destruct x0.
  discriminate.
  discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
Qed.

(* A : Ty & Tm A   <-  pair of a type and a term of that type, constructor: existT _ _ *)
Locate "&".
Print sigT.

Definition vector (n : nat) := { l : list nat & List.length l = n }.
Example vec : vector 5.
  apply (existT _ (1 :: 2 :: 3 :: 4 :: 5 :: nil)).
  simpl. reflexivity.
Defined.

Example vec' : vector 5 := existT _ (1 :: 2 :: 3 :: 4 :: 5 :: nil) eq_refl.

Example p : nat * nat.
Proof.
  split.
  exact 3.
  exact 5.
Defined.

Example p' : nat * nat := pair 3 5.

Goal p = p'.
Proof. reflexivity. Qed.

(**
  Type inference
  EXE: finish it! *)
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
  | U.num t => Some (existT _ Nat (num t))
  | U.isZero t =>
    match infer t with
    | Some (existT _ Nat t') => Some (existT _ Bool(isZero t'))
    | _ => None
    end
  | U.plus t u =>
    match infer t, infer u with
    | Some (existT _ Nat t'),
      Some (existT _ Nat u') => Some (existT _ Nat(plus t' u'))
    | _, _ => None
    end
  end.

(* EXE *)
Goal infer (U.ite (U.num 1) U.true U.false) = None.
  simpl. reflexivity.
Qed.

(* EXE *)
Goal infer (U.ite U.true U.false (U.num 1)) = None.
  simpl. reflexivity.
Qed.

(* EXE *)
Goal infer (U.plus U.true (U.num 1)) = None.
  simpl. reflexivity.
Qed.

(* EXE *)
(* to make this work, you need to have filled in infer *)
Goal infer (U.plus (U.num 2) (U.num 1)) = Some (existT _ Nat (plus (num 2) (num 1))).
  simpl. reflexivity.
Qed.

(* EXE *)
Goal ~ infer (U.plus (U.num 0) (U.num 1)) = Some (existT _ Nat (num 1)).
(* TEACHER: remove solution before tutorial *)
  simpl. unfold not. discriminate.
Qed.
  
(* EXE *)
Goal exists (t : Tm Nat), infer (U.plus (U.num 0) (U.ite (U.isZero (U.num 1)) (U.num 1) (U.num 2))) = Some (existT _ Nat t).
  simpl. exists ((num 0 + ite (isZero (num 1)) (num 1) (num 2))). reflexivity.
Qed.

(* EXE *)
Goal exists (A : Ty)(t : Tm A), infer (U.ite U.false (U.ite U.true (U.num 1) (U.num 2)) (U.plus (U.num 2) (U.num 3))) = Some (existT _ A t).
  simpl. exists Nat. exists (ite false (ite true (num 1) (num 2)) (num 2 + num 3)). reflexivity.
Qed.

(* EXE - correctness of infer *)
Lemma correctInfer (A : Ty)(a : Tm A) : infer ⟦ a ⟧ = Some (existT _ A a).
Proof.
  induction a.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * induction (ite a1 a2 a3) eqn:H1.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - rewrite <- H1. simpl. rewrite IHa1, IHa2, IHa3. simpl. admit.
    - admit.
    - admit.
    - admit.
  * simpl. reflexivity.
  * simpl. rewrite IHa. reflexivity.
  * simpl. rewrite IHa1, IHa2. reflexivity.
Admitted.

(* homework: harder, you need lots of `destruct _ eqn:_` *)
Lemma inferCorrect (t : U.Tm)(A : Ty)(a : Tm A) :
   infer t = Some (existT _ A a) -> ⟦ a ⟧ = t.
Proof.
  revert A a.
  induction t ; intros ; simpl in H.
  inversion H ; subst ; simpl ; reflexivity.
  inversion H ; subst ; simpl ; reflexivity.
  destruct (infer t1). destruct s. destruct x.
  destruct (infer t2). destruct s. destruct x.
  destruct (infer t3). destruct s. destruct x.
  inversion H. subst. simpl.
  rewrite IHt1, IHt2, IHt3 ; reflexivity.
  discriminate.
  discriminate.
  destruct (infer t3). destruct s, x. discriminate.
  inversion H ; subst. simpl.
  rewrite IHt1, IHt2, IHt3 ; reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  admit.
  admit.
  admit.
Admitted.

(* EXE: use correctInfer and/or inferCorrect (do this without rewriting the untyped program in a typed way) *)
Definition t : U.Tm := U.ite (U.isZero (U.plus (U.num 0) (U.num 1))) U.false (U.isZero (U.num 0)).
Goal exists (A : Ty)(a : Tm A), ⟦ a ⟧ = t.
Proof.
  exists Bool.
  induction t eqn:H1.
  * exists true. reflexivity.
  * exists false. reflexivity.
  * exists true. destruct (U.ite t0_1 t0_2 t0_3) eqn:H2.
    - simpl. reflexivity.
    - simpl. discriminate.
    - discriminate. admit.
    - discriminate.
    - discriminate.
    - discriminate.
  * exists true. discriminate.
  * exists true. discriminate.
  * exists true. discriminate.
Admitted.

(* EXE: use correctInfer and/or inferCorrect (do this without rewriting the untyped program in a typed way) *)
Goal ~ exists (A : Ty)(a : Tm A), ⟦ a ⟧ = U.ite U.true U.true (U.num 0).
Admitted.

(* EXE *)
Goal ~ exists (A : Ty)(a : Tm A), ⟦ a ⟧ = U.ite (U.num 0) (U.num 1) (U.num 0).
Proof.
Admitted.

(* EXE *)
Goal ~ exists (A : Ty)(a : Tm A), ⟦ a ⟧ = (U.plus U.true (U.num 1)).
Proof.
Admitted.

(* EXE *)
Goal ~ exists (A : Ty)(a : Tm A), ⟦ a ⟧ = (U.plus (U.isZero (U.num 1)) (U.num 1)).
Proof.
Admitted.

(* EXE *)
Goal ~ exists (A : Ty)(a : Tm A), ⟦ a ⟧ = U.ite U.true U.false (U.num 1).
Proof.
Admitted.

Definition evalTy (A : Ty) : Type := match A with
                                     | Nat => nat
                                     | Bool => bool
                                     end.

(* EXE: write a type-correct evaluator *)
Fixpoint evalTm (A : Ty)(t : Tm A) : evalTy A.
  induction t.
  * (* t = true *) simpl. exact true'.
  * exact false'.
  * (* b' : evalTy Bool, u' : evalTy A, v' : evalTy A *) destruct IHt1.
    - exact IHt2.
    - exact IHt3.
  * simpl. exact n.
  * simpl. destruct IHt.
    - exact true'.
    - exact false'.
  * simpl.
    
    
(* EXE *)
Example notEq : exists A : Ty, exists t1 t2 : Tm A, ~ t1 = t2 /\ evalTm A t1 = evalTm A t2.
Admitted.
    
End Typed.

Module EquationalTheory.
(**
  Now Razor is a GAT, we even know its equational theory (how to run programs, which programs should be equal).
*)

Parameter (Ty : Type).
Parameter (Bool : Ty).
Parameter (Nat : Ty).

Parameter (Tm : Ty -> Type).
Parameter (true   : Tm Bool).
Parameter (false  : Tm Bool).
Parameter (ite    : forall{A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A).
Parameter (num    : nat -> Tm Nat).
Parameter (isZero : Tm Nat -> Tm Bool).
Parameter (plus   : Tm Nat -> Tm Nat -> Tm Nat).
Notation "x + y" := (plus x y) (at level 50, left associativity).

(* semantical equations *)
Parameter (iteβ₁  : forall{A}{u v : Tm A}, ite true u v = u).
Parameter (iteβ₂  : forall{A}{u v : Tm A}, ite false u v = v).
Parameter (isZeroβ₁ : isZero (num 0) = true).
Parameter (isZeroβ₂ : forall{n}, isZero (num (1 + n)) = false).
Parameter (plusβ    : forall{m n}, plus (num m) (num n) = num (m + n)).
(*
  \beta = β
  \_1 = ₁
  \_2 = ₂
*)

(* EXE *)
Goal ite (isZero (num 0 + num 1)) false (isZero (num 0)) = true.
Admitted.

(* EXE *)
Goal exists n, ite (isZero (num 0 + num 0)) (num 10) (num 20) = num n.
Admitted.

(* EXE *)
Goal forall n t, exists (b : bool), ite (isZero (num 0 + num 0)) (num 0 + num n) t = num n.
Admitted.

(* EXE *)
Goal true = false -> forall(A : Ty)(a a' : Tm A), a = a'.
Admitted.
  
(* EXE *)
Goal num 0 = num 1 -> forall(A : Ty)(a a' : Tm A), a = a'.
Proof.
Admitted.

(* EXE: can we prove this?
   If yes, prove it!
   If not, how do we change the language so that it can be proven? *)
Goal num 1 = num 2 -> forall(A : Ty)(a a' : Tm A), a = a'.
Proof.
Admitted.

End EquationalTheory.

(* EXE: extend the language with a <= operator, and do all the exercises above!
   EXE: extend the language with a - operator, and do all the exercises above!
   EXE: create example derivations with the new language!
 *)


Module STLC.

Parameter (Ty : Type).
Parameter (Bool : Ty).
Parameter (Nat : Ty).

Parameter (Tm : Ty -> Type).
Parameter (true   : Tm Bool).
Parameter (false  : Tm Bool).
Parameter (ite    : forall{A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A).
Parameter (num    : nat -> Tm Nat).
Parameter (isZero : Tm Nat -> Tm Bool).
Parameter (plus   : Tm Nat -> Tm Nat -> Tm Nat).
Notation "x + y" := (plus x y) (at level 50, left associativity).

(* semantical equations *)
Parameter (iteβ₁  : forall{A}{u v : Tm A}, ite true u v = u).
Parameter (iteβ₂  : forall{A}{u v : Tm A}, ite false u v = v).
Parameter (isZeroβ₁ : isZero (num 0) = true).
Parameter (isZeroβ₂ : forall{n}, isZero (num (1 + n)) = false).
Parameter (plusβ    : forall{m n}, plus (num m) (num n) = num (m + n)).

Parameter arr  : Ty -> Ty -> Ty.
Notation "x ⇒ y" := (arr x y) (at level 80, right associativity).

Parameter app  : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y" := (app x y) (at level 50, left associativity).
Parameter lam  : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).

Parameter arrβ : forall {A B : Ty}(b : Tm A -> Tm B)(a : Tm A), lam b ⋅ a = b a.
Parameter arrη : forall {A B : Ty}(f : Tm (A ⇒ B)), f = lam (fun x => f ⋅ x).

Definition add2 : Tm (Nat ⇒ Nat) := lam (fun x => plus x (num 2)).
Goal add2 ⋅ num 3 = num 5.
Admitted.

Definition apply2x : Tm ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat). Admitted.
Goal apply2x ⋅ add2 ⋅ num 3 = num 7.
Admitted.

Definition neg : Tm (Bool ⇒ Bool) := lam (fun b => ite b false true).
Goal neg ⋅ true = false. Proof. Admitted.
Goal neg ⋅ false = true. Proof. Admitted.

Definition and : Tm (Bool ⇒ Bool ⇒ Bool). Admitted.  (* λ b c . ite b (ite c true false) (ite c false false) *)

Definition and' : Tm (Bool ⇒ Bool ⇒ Bool). Admitted. (* λ b c . ite b c false *)

Goal and  ⋅ true ⋅ false = false. Admitted.
Goal and' ⋅ true ⋅ false = false. Admitted.
Goal and  ⋅ true ⋅ true = true. Admitted.
Goal and' ⋅ true ⋅ true = true. Admitted.
Goal forall (b : Tm Bool), and' ⋅ true ⋅ b = b. Admitted.

Goal forall b, and' ⋅ b ⋅ false = false. Admitted.
Goal forall a b, and ⋅ a ⋅ b = and ⋅ b ⋅ a. Admitted. (* this is not provable! *)

Definition or : Tm (Bool ⇒ Bool ⇒ Bool). Admitted.
Goal forall b, or ⋅ true ⋅ b = true. Proof. Admitted.
Goal forall b, or ⋅ false ⋅ b = b. Proof. Admitted.
Goal forall a b, or ⋅ a ⋅ b = or ⋅ b ⋅ a. Proof. Admitted. (* not provable *)

(* for every type A, Tm (A ⇒ A) is a monoid *)
Definition comp' {A} : Tm ((A ⇒ A) ⇒ (A ⇒ A) ⇒ (A ⇒ A)) :=
  lam (fun f => lam (fun g => lam (fun x => f ⋅ (g ⋅ x)))).
Notation "f ⊚ g" := (comp' ⋅ f ⋅ g) (at level 50, left associativity). (* \ocir = ⊚ *)
Definition id {A} : Tm (A ⇒ A) := lam (fun a => a).

Goal forall A (f g h : Tm (A ⇒ A)), (f ⊚ g) ⊚ h = f ⊚ (g ⊚ h).
  Admitted.

Goal forall A (f : Tm (A ⇒ A)), f ⊚ id = f. Admitted.

Goal forall A (f : Tm (A ⇒ A)), id ⊚ f = f.
Proof.
Admitted.

(* types form a category *)
Definition comp {A B C} : Tm ((B ⇒ A) ⇒ (C ⇒ B) ⇒ (C ⇒ A)) :=
  lam (fun f => lam (fun g => lam (fun x => f ⋅ (g ⋅ x)))).
Notation "f ∘ g" := (comp ⋅ f ⋅ g) (at level 40, left associativity). (* \circ *)

Goal forall A B C D (f : Tm (B ⇒ A))(g : Tm (C ⇒ B))(h : Tm (D ⇒ C)), (f ∘ g) ∘ h = f ∘ (g ∘ h).
Proof.  Admitted.
Goal forall A B (f : Tm (B ⇒ A)), id ∘ f = f. Proof. Admitted.
Goal forall A B (f : Tm (B ⇒ A)), f ∘ id = f. Proof. Admitted.

Definition K {A B : Ty} : Tm (A ⇒ B ⇒ A) := lam (fun a => lam (fun _ => a)).
Goal forall {A B : Ty} {u : Tm A} {f : Tm B}, K ⋅ u ⋅ f = u.
Proof. Admitted.
Definition S {A B C : Ty} : Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) := lam (fun f => lam (fun g => lam (fun a => f ⋅ a ⋅ (g ⋅ a)))).
Goal forall {A B C : Ty} {f : Tm(A ⇒ B ⇒ C)} {g : Tm(A ⇒ B)} {u : Tm A}, S ⋅ f ⋅ g ⋅ u = f ⋅ u ⋅ (g ⋅ u). Admitted.

End STLC.
