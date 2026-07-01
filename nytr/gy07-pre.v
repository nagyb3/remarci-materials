Require Import FunctionalExtensionality Setoid.
(*
   This is only here to suppress a warning. It will only be used for
   non-compulsory material at the end of this file.
 *)
Require Ring.

Module Finite.

Parameter Ty : Type.
Parameter Tm : Ty -> Type.

Parameter arr        : Ty -> Ty -> Ty.
Notation "A ⇒ B"     := (arr A B) (at level 80, right associativity). (* \Rightarrow *)
Parameter app        : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y"     := (app x y) (at level 50, left associativity). (* \cdot *)
Parameter lam        : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 51, x name, only parsing). (* \lambda *)
Parameter arrβ       : forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a. (* \beta *)
Parameter arrη       : forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun a => f ⋅ a). (* \eta *)

Parameter Prod   : Ty -> Ty -> Ty.
Notation "A × B" := (Prod A B) (at level 78, right associativity). (* \times *)
Parameter pair   : forall {A B}, Tm A -> Tm B -> Tm (A × B).
Notation "x , y" := (pair x y) (at level 80, right associativity).
Parameter fst    : forall {A B}, Tm (A × B) -> Tm A.
Parameter snd    : forall {A B}, Tm (A × B) -> Tm B.
Parameter Prodβ₁ : forall {A B} (a : Tm A) (b : Tm B), fst (a , b) = a.
Parameter Prodβ₂ : forall {A B} (a : Tm A) (b : Tm B), snd (a , b) = b.
Parameter Prodη  : forall {A B} (ab : Tm (A × B)), ab = (fst ab , snd ab).

(* Roppan⊤ bo⊤⊤al koppan⊤o⊤⊤am... *)
Parameter Unit  : Ty.
Notation "⊤"    := Unit. (* \top *)
Parameter tt    : Tm ⊤.
Parameter Unitη : forall (t : Tm ⊤), t = tt.

Parameter Sum    : Ty -> Ty -> Ty.
Notation "A ⊎ B" := (Sum A B) (at level 79, right associativity). (* \uplus *)
Parameter inl    : forall {A B}, Tm A -> Tm (A ⊎ B).
Parameter inr    : forall {A B}, Tm B -> Tm (A ⊎ B).
Parameter case   : forall {A B C}, Tm (A ⊎ B) -> (Tm A -> Tm C) -> (Tm B -> Tm C) -> Tm C.
Parameter Sumβ₁  : forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (a : Tm A), case (inl a) cl cr = cl a.
Parameter Sumβ₂  : forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (b : Tm B), case (inr b) cl cr = cr b.
Parameter Sumη   : forall {A B C} (c : Tm (A ⊎ B) -> Tm C) (ab : Tm (A ⊎ B)), c ab = case ab (fun a => c (inl a)) (fun b => c (inr b)).

Parameter Empty   : Ty.
Notation "⊥"      := Empty. (* \bot *)
Parameter exfalso : forall {A : Ty}, Tm ⊥ -> Tm A.
Parameter Emptyη  : forall {A : Ty} (a : Tm ⊥ -> Tm A) (t : Tm ⊥), a t = exfalso t.

(* We encode the two-valued type with (co)product types *)

Definition Bool   := ⊤ ⊎ ⊤.
Definition true   : Tm Bool := inl tt.
Definition false  : Tm Bool := inr tt.
Definition ite {A : Ty} (t : Tm Bool) (u : Tm A) (v : Tm A) : Tm A :=
  case t (fun _ => u) (fun _ => v).

Proposition Boolβ₁ : forall {A} {u v : Tm A}, ite true u v = u.
Proof.
  intros. cbv. rewrite Sumβ₁. reflexivity.
Qed.
Proposition Boolβ₂ : forall {A} {u v : Tm A}, ite false u v = v.
Proof.
  intros. cbv. rewrite Sumβ₂. reflexivity.
Qed.

(*
  (∀ x, x ∈ A <-------> x ∈ B) --> A = B
   λ x, x                        λ x, x + 0
 (∀ x, f x = g x ) --> f = g
 *)

About functional_extensionality.

(* use extensionality and f_equal *)
Proposition Boolη  : forall {A} (t : Tm Bool -> Tm A) (b : Tm Bool),
  t b = ite b (t true) (t false).
Proof.
  intros.
  cbv in *.
  Check Sumη t b.
  rewrite (Sumη t b).
  f_equal.
  extensionality x.
  f_equal.
  f_equal.
  rewrite (Unitη x).
  reflexivity.
  extensionality x.
(*   f_equal.
  f_equal. *)
  rewrite (Unitη x).
  reflexivity.
Qed.

Goal (fun x => x) = (fun x => ite x true false).
Proof.
  extensionality x.
  Check (Boolη (fun x => x ) x).
(*   exact (Boolη (fun x => x ) x). *)
  apply (Boolη id).
Qed.
  
Goal lam (fun x => x) = lam (fun x => ite x true false).
Proof.
Admitted.

Goal lam (fun x => ite x false true) = lam (fun x => ite x false (ite x true true)).
Proof.
Admitted.

(* the general solution for proving equality of functions out of Tm Bool: you first use Boolη on the outside, then you β reduce everything *)

Goal lam (fun x => ite x (ite x false true) true) = lam (fun x => ite x false (ite x true true)).
Proof.
Admitted.

(* there are only four Bool ⇒ Bool terms *)
(* 2^2, mert a Bool-ban két lehetséges érték van *)

(* ⊥ ⊎ A × ⊤ → B *)
(* |B|^(0 + |A| * 1) *)

Definition bb1 : Tm (Bool ⇒ Bool) := lam (fun b => ite b true  true ).
Definition bb2 : Tm (Bool ⇒ Bool) := lam (fun b => ite b true  false).
Definition bb3 : Tm (Bool ⇒ Bool) := lam (fun b => ite b false true ).
Definition bb4 : Tm (Bool ⇒ Bool) := lam (fun b => ite b false false).

Goal bb1 = bb2 -> true = false.
Proof.
  intros.
  Check (fun f => f ⋅ false).
  Check f_equal (fun f => f ⋅ false).
  apply (f_equal (fun f => f ⋅ false)) in H.
  unfold bb1, bb2 in H.
  rewrite ! arrβ in H.
  rewrite Boolη in H.
Admitted.

Goal bb1 = bb3 -> true = false.
Proof.
Admitted.
Goal bb1 = bb4 -> true = false.
Proof.
Admitted.
Goal bb2 = bb3 -> true = false.
Proof.
Admitted.
Goal bb2 = bb4 -> true = false.
Proof.
Admitted.
Goal bb3 = bb4 -> true = false.
Proof.
Admitted.

(* Is this provable? *)
Goal forall (t : Tm (Bool ⇒ Bool)), t = bb1 \/ t = bb2 \/ t = bb3 \/ t = bb4.
Proof.
Admitted.

(* HW: We encode the three-valued type with (co)product types *)
Definition Three := ⊤ ⊎ ⊤ ⊎ ⊤. (* ⊤ ⊎ (⊤ ⊎ ⊤) *)
Definition three0 : Tm Three. Admitted.
Definition three1 : Tm Three. Admitted.
Definition three2 : Tm Three. Admitted.
Definition caseThree : forall {A : Ty}, Tm Three -> Tm A -> Tm A -> Tm A -> Tm A. Admitted.
Proposition Threeβ₁ : forall {A : Ty} {u v w : Tm A}, caseThree three0 u v w = u.
Proof.
Admitted.
Proposition Threeβ₂ : forall {A : Ty} {u v w : Tm A}, caseThree three1 u v w = v.
Proof.
Admitted.
Proposition Threeβ₃ : forall {A : Ty} {u v w : Tm A}, caseThree three2 u v w = w.
Proof.
Admitted.
(* HW: define and prove the η law *)

(* HW: implementing binary homogeneous sums with product and Bool *)
Definition Dup (A : Ty) : Ty := Bool × A.
Definition inlDup {A : Ty} : Tm A -> Tm (Dup A). Admitted.
Definition inrDup {A : Ty} : Tm A -> Tm (Dup A). Admitted.
Definition caseDup {A C : Ty} : Tm (Dup A) -> (Tm A -> Tm C) -> (Tm A -> Tm C) -> Tm C.
Proof.
Admitted.
Proposition Dupβ₁ : forall {A C : Ty} {f g : Tm A -> Tm C} {a : Tm A}, caseDup (inlDup a) f g = f a.
Proof.
Admitted.
Proposition Dupβ₂ : forall {A C : Ty} {f g : Tm A -> Tm C} {a : Tm A}, caseDup (inrDup a) f g = g a.
Proof.
Admitted.
(* HW: define and prove the η law *)

(* TODO: option / maybe *)
Definition Maybe (A : Ty) : Ty := A ⊎ ⊤.
Definition just {A : Ty} (a : Tm A) : Tm (Maybe A) := inl a.
Definition nothing {A : Ty} : Tm (Maybe A) := inr tt.
Definition fromMaybe {A C : Ty} (f : Tm A -> Tm C) (c : Tm C)
  : Tm (Maybe A) -> Tm C
  := fun m => case m (fun a => f a) (fun _ => c).
Proposition Maybeβ₁ : forall {A C : Ty} {f : Tm A -> Tm C} {c : Tm C} {a : Tm A}, fromMaybe f c (just a) = f a.
Proof.
Admitted.
Proposition Maybeβ₂ : forall {A C : Ty} {f : Tm A -> Tm C} {c : Tm C}, fromMaybe f c nothing = c.
Proof.
Admitted.

(* every finite type *)
Fixpoint Fin (n : nat) : Ty := match n with
                               | O => ⊥
                               | S m => ⊤ ⊎ Fin m
                               end.
(* TODO: define its constructors and eliminator *)
Definition fzero {n} : Tm (Fin (S n)) := inl tt.
Definition fsuc {n} (t : Tm (Fin n)) : Tm (Fin (S n)) := inr t.

(* HW: define all n-ary sum and product types (n : nat) *)
Definition NarySum (n : nat) (A : Ty) : Ty. Admitted.

(* TODO: isomorphism *)
Record Iso (A B : Ty) : Prop := mkIso {
  f : Tm A -> Tm B ;
  g : Tm B -> Tm A ;
  gf : forall a, g (f a) = a ;
  fg : forall b, f (g b) = b
}.
Notation "A ≅ B" := (Iso A B) (at level 40). (* \cong *)

(* Exe. 124 *)
Goal forall A, (A × ⊤) ≅ A.
Proof.
  intros.
(*   unshelve eapply mkIso. *)
(*   unshelve esplit. *)
  unshelve eexists.
  
  intros. eapply fst. exact X.
  refine (fun x => x , tt).
  
  Restart. intros.
  
(*   exists fst (fun x => x, tt). *)
(*   split with fst (fun x => x, tt). *)
  apply (mkIso _ _ fst (fun x => x, tt)).
  intros.
  rewrite Prodη, (Unitη (snd a)).
  reflexivity.
  intros. exact (Prodβ₁ b tt).
Qed.

Lemma a_eq_case_inl_inr A B (a : Tm (A ⊎ B)) : a = case a inl inr.
Proof.
Admitted.

Goal forall A, (A ⊎ ⊥) ≅ A.
Proof.
Admitted.

(* Exe. 125 *)
Goal forall A B, (A ⊎ B) ≅ (B ⊎ A).
Proof.
Admitted.

Goal forall A B, (A × B) ≅ (B × A).
Proof.
Admitted.

(* Exe. 126 *)
Goal
  forall A B, (Bool ⇒ A ⊎ B) ≅ ((Bool ⇒ A) ⊎ Bool × A × B ⊎ (Bool ⇒ B)).
Proof.
Admitted.

(* Exe. 127 *)
Lemma iso_refl :
  forall A, A ≅ A.
Proof.
Admitted.

Lemma iso_sym :
  forall A B, A ≅ B -> B ≅ A.
Proof.
Admitted.

Lemma iso_trans :
  forall A B C, A ≅ B -> B ≅ C -> A ≅ C.
Proof.
  intros.
  destruct H, H0.
(*   unshelve esplit.
  intros. apply f0, f, X.
  exact (fun c => g (g0 c)). *)
  exists (fun a => f0 (f a)) (fun c => g (g0 c)).
  intros. rewrite gf0. rewrite gf. reflexivity.
  intros. rewrite fg. rewrite fg0. reflexivity.
Qed.

Lemma iso_prod_cong_l :
  forall A B, A ≅ B -> forall C, (A × C) ≅ (B × C).
Proof.
Admitted.

Lemma iso_prod_cong_r :
  forall A B, A ≅ B -> forall C, (C × A) ≅ (C × B).
Proof.
Admitted.

Lemma iso_sum_cong_l :
  forall A B, A ≅ B -> forall C, (A ⊎ C) ≅ (B ⊎ C).
Proof.
Admitted.

Lemma iso_sum_cong_r :
  forall A B, A ≅ B -> forall C, (C ⊎ A) ≅ (C ⊎ B).
Proof.
Admitted.

Lemma iso_exp_cong_l :
  forall A B, A ≅ B -> forall C, (A ⇒ C) ≅ (B ⇒ C).
Proof.
Admitted.

Lemma iso_exp_cong_r :
  forall A B, A ≅ B -> forall C, (C ⇒ A) ≅ (C ⇒ B).
Proof.
Admitted.

(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* Idáig érdemes megoldani, a kiszh inkább az elejébol lesz, mint a végébol. *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

(* Prove that the sum, product, and function types make an exponential
semiring *)
(*
  a + 0 = a
  a + b = b + a
  a + (b + c) = (a + b) + c
  a * 1 = a
  ...

  arr is exponentiation
  (a => b) == b^a

  (a => (b => c)) = (a * b => c)
*)

(*
   Coq has powerful mechanisms built in for reasoning with these structures.
   Once you provide the (relatively) simple proofs, complex goals can be
   solved by the automated tactics. First, we must prove that isomorphism
   over types is an equivalence relation, and that sum and product types are
   morphisms over this relation.
*)

Add Parametric Relation : Ty (Iso)
  reflexivity proved by iso_refl
  symmetry proved by iso_sym
  transitivity proved by iso_trans
  as Iso_rel.

Add Parametric Morphism : Prod
  with signature Iso ==> Iso ==> Iso as Prod_morph.
Proof.
  intros * [] * [].
  exists
    (fun x => (f (fst x) , f0 (snd x)))
    (fun y => (g (fst y) , g0 (snd y)));
  intros;
  now rewrite Prodβ₁, Prodβ₂, ? fg, ? gf, ? fg0, ? gf0, Prodη.
Qed.

Add Parametric Morphism : Sum
  with signature Iso ==> Iso ==> Iso as Sum_morph.
Proof.
  intros * [] * [].
  exists
    (fun x => case x (fun x' => inl (f x')) (fun x' => inr (f0 x')))
    (fun y => case y (fun y' => inl (g y')) (fun y' => inr (g0 y')));
  intros.
  rewrite (Sumη (fun X => case (case X (fun x' : Tm x => inl (f x')) (fun x' : Tm x0 => inr (f0 x'))) (fun y' : Tm y => inl (g y')) (fun y' : Tm y0 => inr (g0 y'))) a).
  rewrite a_eq_case_inl_inr.
  f_equal; extensionality X.
  now rewrite ! Sumβ₁, gf.
  now rewrite ! Sumβ₂, gf0.
  rewrite (Sumη (fun X => case (case X (fun y' : Tm y => inl (g y')) (fun y' : Tm y0 => inr (g0 y'))) (fun x' : Tm x => inl (f x')) (fun x' : Tm x0 => inr (f0 x'))) b).
  rewrite a_eq_case_inl_inr.
  f_equal; extensionality X.
  now rewrite ! Sumβ₁, fg.
  now rewrite ! Sumβ₂, fg0.
Qed.

(*
   Now the setoid-prefixed tactics are usable to easily solve these kinds of
   goals. See [the documentation] for more detail. We can also define a
   semiring structure over these definitions.

   [the documentation]: https://rocq-prover.org/doc/V8.20.0/refman/addendum/generalized-rewriting.html
 *)

Goal forall A B C, A ≅ B -> (A × C ⊎ A) ≅ (B × C ⊎ B).
Proof.
  intros.
  setoid_rewrite H.
  setoid_reflexivity.
Qed.

Import Ring.

Print semi_ring_theory.

(* HW: finish this *)
Definition Ty_semi_ring_theory : @semi_ring_theory Ty Empty Unit Sum Prod Iso.
Proof.
  split; intros.
  - exists (fun x => case x exfalso id) inr; intros.
    + rewrite (Sumη (fun x => inr (case x exfalso id)) a).
      rewrite a_eq_case_inl_inr.
      f_equal; extensionality x.
      rewrite Sumβ₁.
      rewrite (Emptyη (fun x => inr (exfalso x))).
      rewrite (Emptyη inl). reflexivity.
      rewrite Sumβ₂. reflexivity.
    + now rewrite Sumβ₂.
  - exists (fun x => case x inr inl) (fun x => case x inr inl); intros.
    + rewrite (Sumη (fun x => case (case x inr inl) inr inl) a).
      rewrite a_eq_case_inl_inr. f_equal; extensionality x;
      now repeat rewrite ? Sumβ₁, ? Sumβ₂.
    + rewrite (Sumη (fun x => case (case x inr inl) inr inl) b).
      rewrite a_eq_case_inl_inr. f_equal; extensionality x;
      now repeat rewrite ? Sumβ₁, ? Sumβ₂.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

(*
   Exponentiation can supposedly be expressed with this, but it's
   undocumented. If you figure it out, please send it to us.
 *)
Print power_theory.

Add Ring Ty_semi_ring : Ty_semi_ring_theory
  (* (power <put_above_thing_here>) *)
  .

(*
   Now even goals like this are automatically proven. See [the other
   documentation] for more detail. Unfortunately, it is incomplete.

   [the other documentation]: https://rocq-prover.org/doc/V8.20.0/refman/addendum/ring.html
*)

Goal forall A B C, (A × B × C) ≅ (C × A × B).
Proof.
  intros.
  ring.
Qed.

End Finite.
