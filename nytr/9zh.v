(* BEGIN FIX *)
Require Import Setoid.

Parameter Ty : Type.
Parameter Tm : Ty -> Type.

Parameter arr        :  Ty -> Ty -> Ty.
Notation "A ⇒ B"     := (arr A B) (at level 80, right associativity).
Parameter app        :  forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y"     := (app x y) (at level 50, left associativity).
Parameter lam        :  forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 81, x name).
Parameter arrβ       :  forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a.
Parameter arrη       :  forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun a => f ⋅ a).

Parameter Prod   :  Ty -> Ty -> Ty.
Notation "A × B" := (Prod A B) (at level 78, right associativity). (* \times *)
Parameter pair   :  forall {A B}, Tm A -> Tm B -> Tm (A × B).
Notation "x , y" := (pair x y) (at level 80, right associativity).
Parameter fst    :  forall {A B}, Tm (A × B) -> Tm A.
Parameter snd    :  forall {A B}, Tm (A × B) -> Tm B.
Parameter Prodβ₁ :  forall {A B} (a : Tm A) (b : Tm B), fst (a , b) = a.
Parameter Prodβ₂ :  forall {A B} (a : Tm A) (b : Tm B), snd (a , b) = b.
Parameter Prodη  :  forall {A B} (ab : Tm (A × B)), ab = (fst ab , snd ab).

Parameter Unit  :  Ty.
Notation "⊤"    := Unit. (* \top *)
Parameter tt    :  Tm ⊤.
Parameter Unitη :  forall (t : Tm ⊤), t = tt.

Parameter Sum    :  Ty -> Ty -> Ty.
Notation "A ⊎ B" := (Sum A B) (at level 79, right associativity). (* \uplus *)
Parameter inl    :  forall {A B}, Tm A -> Tm (A ⊎ B).
Parameter inr    :  forall {A B}, Tm B -> Tm (A ⊎ B).
Parameter case   :  forall {A B C}, Tm (A ⊎ B) -> (Tm A -> Tm C) -> (Tm B -> Tm C) -> Tm C.
Parameter Sumβ₁  :  forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (a : Tm A), case (inl a) cl cr = cl a.
Parameter Sumβ₂  :  forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (b : Tm B), case (inr b) cl cr = cr b.
Parameter Sumη   :  forall {A B C} (c : Tm (A ⊎ B) -> Tm C) (w : Tm (A ⊎ B)), c w = case w (fun a => c (inl a)) (fun b => c (inr b)).

Parameter Empty   :  Ty.
Notation "⊥"      := Empty. (* \bot *)
Parameter exfalso :  forall {A : Ty}, Tm ⊥ -> Tm A.
Parameter Emptyη  :  forall {A : Ty} (a : Tm ⊥ -> Tm A) (w : Tm ⊥), a w = exfalso w.

Inductive SPos : (Ty -> Ty) -> Type :=
  | idP    : SPos (fun X => X)
  | constP : forall (A : Ty), SPos (fun _ => A)
  | ProdP  : forall {F G}, SPos F -> SPos G -> SPos (fun X => F X × G X)
  | SumP   : forall {F G}, SPos F -> SPos G -> SPos (fun X => F X ⊎ G X)
  | ArrP   : forall {F} (A : Ty), SPos F -> SPos (fun X => A ⇒ F X)
.

Fixpoint map {F : Ty -> Ty} {A B : Ty} (FP : SPos F) (f : Tm A -> Tm B) : Tm (F A) -> Tm (F B) :=
  match FP in SPos F return Tm (F A) -> Tm (F B) with
  | idP         => f
  | constP A    => id
  | ProdP FP GP => fun t => (map FP f (fst t), map GP f (snd t))
  | SumP  FP GP => fun t => case t (fun u => inl (map FP f u)) (fun v => inr (map GP f v))
  | ArrP   A FP => fun t => lam (fun x => map FP f (t ⋅ x))
  end.

Parameter Ind    : forall {F : Ty -> Ty}, SPos F -> Ty.
Parameter con    : forall {F : Ty -> Ty} (FP : SPos F), Tm (F (Ind FP)) -> Tm (Ind FP).
Parameter iteInd : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty}, (Tm (F C) -> Tm C) -> Tm (Ind FP) -> Tm C.
Parameter Indβ   : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm (F C) -> Tm C) (w : Tm (F (Ind FP))),
  iteInd FP f (con FP w) = f (map FP (iteInd FP f) w).
Parameter Indη   : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm (F C) -> Tm C) (z : Tm (Ind FP) -> Tm C),
  (forall (w : Tm (F (Ind FP))), z (con FP w) = f (map FP z w)) -> z = iteInd FP f.

Definition FNat : Ty -> Ty := fun X => ⊤ ⊎ X.

Lemma NatP : SPos FNat.
Proof.
  unfold FNat.
  apply SumP. apply constP. apply idP.
Defined.

Definition Nat : Ty := Ind NatP.

Definition zero : Tm Nat := con _ (inl tt).
Definition suc (n : Tm Nat) : Tm Nat := con _ (inr n).

Definition iteNat {C} (z : Tm C) (s : Tm C -> Tm C) (n : Tm Nat) : Tm C := iteInd _ (fun x => case x (fun _ => z) (fun y => s y)) n.

Lemma Natβ₁ : forall C {z : Tm C} {s : Tm C -> Tm C}, iteNat z s zero = z.
Proof.
  intros.
  cbv. rewrite Indβ.
  cbv. rewrite ! Sumβ₁.
  reflexivity.
Qed.

Lemma Natβ₂ : forall C {z : Tm C} {s : Tm C -> Tm C} {n : Tm Nat}, iteNat z s (suc n) = s (iteNat z s n).
Proof.
  intros.
  cbv. rewrite Indβ.
  cbv. rewrite ! Sumβ₂.
  reflexivity.
Qed.

Definition plus (a b : Tm Nat) : Tm Nat := iteNat b suc a.

Definition NatListF : Ty -> Ty := fun X => ⊤ ⊎ Nat × X.

Lemma NatListP : SPos NatListF.
Proof.
(* END FIX *)
  unfold NatListF.
  apply SumP.
  apply constP.
  apply ProdP.
  apply constP.
  apply idP.
(* BEGIN FIX *)
Defined.

Definition NatList : Ty := Ind NatListP.

Definition nil : Tm NatList :=
(* END FIX *)
  con NatListP (inl tt)
(* BEGIN FIX *)
.
Definition cons (x : Tm Nat) (xs : Tm NatList) : Tm NatList :=
(* END FIX *)
  con NatListP (inr (x, xs))
(* BEGIN FIX *)
.

Definition iteNatList {C} (n : Tm C) (c : Tm Nat -> Tm C -> Tm C) (l : Tm NatList) : Tm C :=
(* END FIX *)
  iteInd NatListP (fun x => case x (fun _ => n) (fun y => c (fst y) (snd y))) l
(* BEGIN FIX *)
.

Lemma NatListβ₁ C (n : Tm C) c : iteNatList n c nil = n.
Proof.
(* END FIX *)
  cbv.
  rewrite ! Indβ.
  cbv.
  rewrite ! Sumβ₁.
  reflexivity.
(* BEGIN FIX *)
Qed.

Lemma NatListβ₂ C (n : Tm C) c x xs : iteNatList n c (cons x xs) = c x (iteNatList n c xs).
Proof.
(* END FIX *)
  cbv.
  rewrite ! Indβ.
  cbv.
  rewrite ! Sumβ₂.
  rewrite ! Prodβ₁.
  rewrite ! Prodβ₂.
  reflexivity.
(* BEGIN FIX *)
Qed.

Definition sum (xs : Tm NatList) : Tm Nat := iteNatList zero plus xs.

Definition one : Tm Nat := suc zero.
Definition two : Tm Nat := suc one.
Definition three : Tm Nat := suc two.

Goal sum (cons one (cons two nil)) = three.
Proof.
  unfold sum. rewrite ! NatListβ₂, NatListβ₁.
  unfold plus, three, two, one. rewrite ! Natβ₂, ! Natβ₁.
  reflexivity.
Qed.
(* END FIX *)
