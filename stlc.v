Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.

Opaque lt_eq_lt_dec.

(** Terms *)
Inductive Trm : Type :=
| Trm_Unit : Trm
| Trm_Var : nat -> Trm
| Trm_Func : Trm -> Trm
| Trm_App : Trm -> Trm -> Trm
.

Notation un := (Trm_Unit).
Notation "𝔳( n )" := (Trm_Var n).
Notation "'λ' f" := (Trm_Func f) (at level 0).
Notation "x · y" := (Trm_App x y) (at level 50, y at next level, left associativity).

(** Types *)
Inductive Typ  : Type :=
| Typ_Unit : Typ
| Typ_Func : Typ -> Typ -> Typ
.

Notation Un := (Typ_Unit).
Notation "A —≻ B" := (Typ_Func A B) (at level 99, right associativity).

(** A context is just a list of types.
The head of the list is the type of the variable 0. *)
Inductive Context :=
| Emp : Context
| Cons : Typ -> Context -> Context
.

Notation ε := Emp.
Notation "A , C" := (Cons A C) (at level 100).

Reserved Notation "Δ +++ Γ" (at level 60, right associativity).

Fixpoint ContextCompose (Δ Γ : Context) : Context :=
  match Δ with
  | ε => Γ
  | (A, Δ') => A, Δ' +++ Γ
  end
where "Δ +++ Γ" := (ContextCompose Δ Γ)
.

Fixpoint CLen (Γ : Context) : nat :=
  match Γ with
  | ε => O
  | (A, Γ') => S (CLen Γ')
  end
.

Reserved Notation "[ Γ ] ⊢ t ::: T" (at level 100, no associativity).

(** Typing relation *)
Inductive Typed : Context -> Trm -> Typ -> Prop :=
| Tpd_Un : forall (Γ: Context), [Γ] ⊢ un ::: Un
| Tpd_Var : forall (T : Typ) (Γ Γ' : Context),
    [Γ +++ (T, Γ')] ⊢ 𝔳(CLen Γ) ::: T
| Tpd_Func : forall (Γ : Context) (t : Trm) (T T' : Typ),
    ([T, Γ] ⊢ t ::: T') -> ([Γ] ⊢ (λ t) ::: (T —≻ T'))
| Tpd_App : forall (Γ : Context) (t t' : Trm) (T T' : Typ),
    ([Γ] ⊢ t ::: (T —≻ T')) -> ([Γ] ⊢ t' ::: T) -> ([Γ] ⊢ (t · t') ::: T')
where "[ Γ ] ⊢ t ::: T " := (Typed Γ t T).


Theorem not_lt_O : forall n, ~ (n < 0).
Proof.
  intros n H.
  inversion H.
Qed.

(** shift free m-variables (greater than or equal to  m) by n. *)
Fixpoint shift (n : nat) (m : nat) (t : Trm) : Trm :=
  match t with
  | un => un
  | 𝔳(y) => if le_dec m y then 𝔳(n + y) else 𝔳(y)
  | λ f => λ (shift n (S m) f)
  | t1 · t2 => (shift n m t1) · (shift n (m) t2)
  end
.

Reserved Notation "t [ x // m ]" (at level 100, no associativity).

(** substitution *)
Fixpoint subst (t : Trm) (x : nat) (m : Trm) : Trm :=
  match t with
  | un => un
  | 𝔳(y) =>
    match lt_eq_lt_dec x y with
    | inleft H =>
      match H with
      | left H' =>
        (match y as u return x < u -> Trm with
         | O => fun G => False_rect _ (not_lt_O _ G)
         | S y' => fun G => 𝔳(y')
         end)
          H'
      | right _ => m
      end
    | inright _ =>
      𝔳(y)
    end
  | λ f => λ (f [(S x) // (shift 1 O m)])
  | t1 · t2 => (t1 [x // m]) · (t2 [x // m])
  end
where "t [ x // m ]" := (subst t x m)
.

Theorem shift_O (t : Trm) (m : nat) : shift O m t = t.
Proof.
  revert m.
  induction t; cbn; intros m; trivial; try destruct le_dec; trivial.
  + rewrite <- IHt at 2; trivial.
  + rewrite <- IHt1 at 2; rewrite <- IHt2 at 2; trivial.
Qed.

(** Shifts can be swapped changing their arguments. *)
Theorem shift_shift (t : Trm) (k l m n : nat) :
  shift k l (shift m (l + n) t) = shift m (k + l + n) (shift k l t).
Proof.
  revert k l m n.
  induction t; intros k l m n'; cbn;
  trivial; repeat (try destruct le_dec; cbn);
  trivial; try omega.
  - match goal with
      |- 𝔳(?A) = 𝔳(?B) => replace A with B by omega; trivial
    end.
  - change (S (l + n')) with ((S l) + n').
    rewrite IHt.
    match goal with
      |- _ (shift _ ?A _) = _ (shift _ ?B _) => replace A with B by omega; trivial
    end.
  - rewrite IHt1.
    rewrite IHt2.
    trivial.    
Qed.

Lemma Typed_shift (Δ Δ' Γ : Context) (t : Trm) (T : Typ) :
  ([Δ' +++ Γ]⊢ t ::: T) ->
  [Δ' +++ Δ +++ Γ]⊢ shift (CLen Δ) (CLen Δ') t ::: T
.
Proof.
  intros H.
  remember (Δ' +++ Γ) as ξ.
  revert Δ' Δ Heqξ.
  set (H' := H); clearbody H'.
  induction H; cbn in *.
  + constructor.
  + intros Δ' Δ Heqξ.
    destruct le_dec.
    admit.
    admit.
  + intros Δ' Δ Heqξ.
    constructor.
    change (T, Δ' +++ Δ +++ Γ) with ((T, Δ') +++ Δ +++ Γ).
    apply IHTyped; trivial.
    rewrite Heqξ.
    trivial.
  + intros Δ.
    econstructor; eauto.
Admitted.
      

  (*
Theorem Relevant_Context (Δ Γ : Context) (n : nat) (T : Typ) :
  ([Δ +++ Γ] ⊢ 𝔳(n) ::: T) ->
  (n < CLen Δ) ->
  forall Γ',   ([Δ +++ Γ'] ⊢ 𝔳(n) ::: T)
.
Proof.
  revert n.
  induction Δ; cbn; intros n H1 H2 Γ'.
  + inversion H2.
  + destruct n.
    * inversion H1; subst.
      constructor.
    * constructor.
      apply IHΔ.
      inversion H1; trivial.
      omega.
Qed.      
   *)

Theorem Typed_Subst (Δ Δ' Γ : Context) (t t' : Trm) (T T' : Typ) :
  ([Δ' +++ Γ] ⊢ t' ::: T') ->
  ([Δ' +++ Δ +++ (T', Γ)] ⊢ t ::: T) ->
  ([Δ' +++ Δ +++ Γ] ⊢ t [(CLen (Δ' +++ Δ)) // (shift (CLen Δ) (CLen Δ') t')] ::: T)
.
Proof.
  intros H1 H2.
  remember (Δ' +++ Δ +++ (T', Γ)) as Υ.
  revert Δ Δ' t' HeqΥ H1.
  set (H2' := H2); clearbody H2'.
  induction H2; intros Δ Δ' s HeqΥ H1; cbn in *.
  - constructor.
  - destruct lt_eq_lt_dec as [[G|G]|G].
    + destruct Γ0; [inversion G|]; cbn in *.
      rewrite HeqΥ in H2'.
        admit.
    + apply Typed_shift.
      rewrite HeqΥ in H2'.
      admit.
    + rewrite HeqΥ in H2'.
      admit.
  - constructor.
    set (W := fun t => shift_shift t 1 0); cbn in W; rewrite W; clear W.
    change (T, Δ' +++ Δ +++ Γ) with ((T, Δ') +++ Δ +++ Γ).
    change (S (CLen (Δ' +++ Δ))) with (CLen (T, Δ' +++ Δ)).
    apply IHTyped; trivial.
    + rewrite HeqΥ.
      trivial.
    + admit.
  - econstructor.
    + apply IHTyped1; trivial.
    + apply IHTyped2; trivial.
Admitted.
  
Reserved Notation "s ↝* t" (at level 100, no associativity).

Inductive Red : Trm -> Trm -> Prop :=
| Red_Refl : forall t, t ↝* t
| Red_Trans : forall t1 t2 t3, (t1 ↝* t2) -> (t2 ↝* t3) -> t1 ↝* t3
| Beta : forall (t1 t2: Trm), ((λ t1) · t2) ↝* (t1 [O // t2])
| Red_App1 : forall t1 t2 t13 t23, (t1 ↝* t13) -> (t2 ↝* t23) -> (t1 · t2) ↝* (t13 · t23)
| Red_Func : forall t1 t2, (t1 ↝* t2) -> (λ t1) ↝* (λ t2)
where "s ↝* t" := (Red s t).

Theorem SubjectRed (Γ : Context) (t t' : Trm) (T : Typ) :
        ([Γ] ⊢ t ::: T) -> (t ↝* t') -> ([Γ] ⊢ t' ::: T)
.
Proof.
  intros H1 H2.
  revert Γ T H1.
  induction H2; auto;
  intros Γ T H1; inversion H1; subst;
  try (econstructor; eauto).
  + inversion H3; subst.
    set (W := Typed_Subst ε ε _ _ _ _ _ H5 H4); cbn in W.
    rewrite shift_O in W.
    trivial.
Qed.