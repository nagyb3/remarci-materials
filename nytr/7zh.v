(* BEGIN FIX *)
Require Import FunctionalExtensionality Setoid.

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
Proposition Boolη  : forall {A} (t : Tm Bool -> Tm A) (b : Tm Bool),
  t b = ite b (t true) (t false).
Proof.
  intros. cbv in *.
  rewrite (Sumη t b).
  f_equal. extensionality x.
  rewrite (Unitη x). reflexivity.
  extensionality x. now rewrite (Unitη x).
Qed.

Record Iso (A B : Ty) : Prop := mkIso {
  f : Tm A -> Tm B ;
  g : Tm B -> Tm A ;
  gf : forall a, g (f a) = a ;
  fg : forall b, f (g b) = b
}.
Notation "A ≅ B" := (Iso A B) (at level 80). (* \cong *)

Goal forall A, (Bool ⇒ A) ≅ A × A.
Proof.
(* END FIX *)
  intros.
  unshelve eexists.
  * admit.
  * admit.
  * intros. admit.
  * intros. admit.

  Restart.
  intros.
  exists (fun f =>)
  
(* BEGIN FIX *)
Qed.
(* END FIX *)