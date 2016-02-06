Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.

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
Notation "A ,, C" := (Cons A C) (at level 100).

Reserved Notation "Δ +++ Γ" (at level 60, right associativity).

Fixpoint ContextCompose (Δ Γ : Context) : Context :=
  match Δ with
  | ε => Γ
  | (A,, Δ') => A,, Δ' +++ Γ
  end
where "Δ +++ Γ" := (ContextCompose Δ Γ)
.

Fixpoint CLen (Γ : Context) : nat :=
  match Γ with
  | ε => O
  | (A,, Γ') => S (CLen Γ')
  end
.

Reserved Notation "[ Γ ] ⊢ t ::: T" (at level 100, no associativity).

(** Typing relation *)
Inductive Typed : Context -> Trm -> Typ -> Prop :=
| Tpd_Un : forall (Γ: Context), [Γ] ⊢ un ::: Un
| Tpd_Var : forall (T : Typ) (Γ Γ' : Context),
    [Γ +++ (T,, Γ')] ⊢ 𝔳(CLen Γ) ::: T
| Tpd_Func : forall (Γ : Context) (t : Trm) (T T' : Typ),
    ([T,, Γ] ⊢ t ::: T') -> ([Γ] ⊢ (λ t) ::: (T —≻ T'))
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

Reserved Notation "t [ m // x ]" (at level 100, no associativity).

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
  | λ f => λ (f [(shift 1 O m) // (S x)])
  | t1 · t2 => (t1 [m // x]) · (t2 [m // x])
  end
where "t [ m // x ]" := (subst t x m)
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
    change (T,, Δ' +++ Δ +++ Γ) with ((T,, Δ') +++ Δ +++ Γ).
    apply IHTyped; trivial.
    rewrite Heqξ.
    trivial.
  + intros Δ.
    econstructor; eauto.
Admitted.

Theorem Typed_Subst (Δ Δ' Γ : Context) (t t' : Trm) (T T' : Typ) :
  ([Δ' +++ Γ] ⊢ t' ::: T') ->
  ([Δ' +++ Δ +++ (T',, Γ)] ⊢ t ::: T) ->
  ([Δ' +++ Δ +++ Γ] ⊢ t [(shift (CLen Δ) (CLen Δ') t') // (CLen (Δ' +++ Δ))] ::: T)
.
Proof.
  intros H1 H2.
  remember (Δ' +++ Δ +++ (T',, Γ)) as Υ.
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
    change (T,, Δ' +++ Δ +++ Γ) with ((T,, Δ') +++ Δ +++ Γ).
    change (S (CLen (Δ' +++ Δ))) with (CLen (T,, Δ' +++ Δ)).
    apply IHTyped; trivial.
    + rewrite HeqΥ.
      trivial.
    + admit.
  - econstructor.
    + apply IHTyped1; trivial.
    + apply IHTyped2; trivial.
Admitted.
  
Reserved Notation "s ↝₁ t" (at level 100, no associativity).

Inductive Red1 : Trm -> Trm -> Type :=
| Red_Refl : forall t, t ↝₁ t
| Beta : forall t1 s1 t2 s2, (t1 ↝₁ s1) -> (t2 ↝₁ s2) -> ((λ t1) · t2) ↝₁ (s1 [s2 // O])
| Red_App : forall t1 t2 t13 t23, (t1 ↝₁ t13) -> (t2 ↝₁ t23) -> (t1 · t2) ↝₁ (t13 · t23)
| Red_Func : forall t1 t2, (t1 ↝₁ t2) -> (λ t1) ↝₁ (λ t2)
where "s ↝₁ t" := (Red1 s t).

Hint Constructors Red1.

Theorem SubjectRed1 (Γ : Context) (t t' : Trm) (T : Typ) :
        ([Γ] ⊢ t ::: T) -> (t ↝₁ t') -> ([Γ] ⊢ t' ::: T)
.
Proof.
  intros H1 H2.
  revert Γ T H1.
  induction H2; auto;
  intros Γ T H1; inversion H1; subst;
  try (econstructor; eauto).
  + inversion H3; subst.
    apply IHRed1_1 in H4.
    apply IHRed1_2 in H5.
    set (W := Typed_Subst ε ε _ _ _ _ _ H5 H4); cbn in W.
    rewrite shift_O in W.
    trivial.
Qed.

Lemma unit_red1 (t : Trm) : (un ↝₁ t) -> t = un.
Proof.
  intros H.
  inversion H; auto.
Qed.

Hint Extern 1 =>
match goal with
  [H : un ↝₁ _ |- _] => apply unit_red1 in H; subst
end.

Lemma var_red1 (n : nat) (t : Trm) : (𝔳(n) ↝₁ t) -> t = 𝔳(n).
Proof.
  intros H.
  inversion H; auto.
Qed.

Hint Extern 1 =>
match goal with
  [H : 𝔳(_) ↝₁ _ |- _] => apply var_red1 in H; subst
end.

Lemma fun_red1 (t1 t2 : Trm) : ((λ t1) ↝₁ t2) -> {s : Trm & t2 = λ s & t1 ↝₁ s}.
Proof.
  intros H.
  inversion H; eexists; eauto.
Qed.

Hint Extern 1 =>
match goal with
  [H : (λ _) ↝₁ _ |- _] =>
  apply fun_red1 in H;
    let s := fresh "s" in
    let H1 := fresh "H" in
    let H2 := fresh "H2" in
    destruct H as [s H1 H2];
      subst
end.

Lemma subst_red1 (t1 t2 s1 s2: Trm) (l : nat) :
  (t1 ↝₁ s1) ->
  (t2 ↝₁ s2) ->
  (t1 [t2 // l]) ↝₁ (s1 [s2 // l])
.
Proof.
  intros H1 H2.
  revert s1 H1 t2 s2 l H2.
  induction t1; intros s1 H1 t2 s2 l H2; eauto.
   - apply var_red1 in H1; subst.
     cbn; destruct lt_eq_lt_dec as [[]|]; destruct n; auto.
   - apply fun_red1 in H1; destruct H1 as [v H1]; subst.
     constructor; fold subst.
     apply IHt1; eauto.
     admit.
   - cbn.
     inversion H1; subst; cbn in *; auto.
     + assert (G1 : λ t1 ↝₁ λ s0) by auto.
       specialize (IHt1_1 _ G1 _ _ l H2).
       inversion IHt1_1; subst.
       admit.
       admit.
Admitted.

Hint Resolve subst_red1.

Hint Extern 1 => match goal with [H : λ _ = λ _ |- _] => inversion H; subst end.

Theorem ChurchRosser1 (t s1 s2 : Trm) :
  (t ↝₁ s1) -> (t ↝₁ s2) -> {r : Trm & (s1 ↝₁ r) & (s2 ↝₁ r)}.
Proof.
  revert s1 s2.
  induction t; intros s1 s2 H1 H2; eauto.
  - inversion H1; subst; inversion H2; subst; eauto.
    match goal with
      [H1 : t ↝₁ _ , H2 : t ↝₁ _ |- _] => 
      destruct (IHt _ _ H1 H2); eauto
    end.
  - destruct t1;
    inversion H1; subst; inversion H2; subst; eauto;
    repeat match goal with
             [H1 : ?t ↝₁ ?s1 , H2 : ?t ↝₁ ?s2 |- _] => 
             (destruct (IHt1 _ _ H1 H2); clear H1 H2) +
             (destruct (IHt2 _ _ H1 H2); clear H1 H2) +
             (
               let H1' := fresh "H" in
               let H2' := fresh "H" in
               assert (H1' : (λ t) ↝₁ (λ s1)) by eauto;
                 assert (H2' : (λ t) ↝₁ (λ s2)) by eauto;
                 clear H1 H2;
                 (destruct (IHt1 _ _ H1' H2'); clear H1' H2')
             ) +
             (match goal with
                [H : λ _ ↝₁ ?s |- _] =>
                inversion H; subst; clear H
              end)
           end;
    eauto 7.
Qed.

Reserved Notation "s ↝* t" (at level 100, no associativity).

Inductive Red (t1 : Trm) (t3 : Trm) : Type :=
| Red_Red1 : (t1 ↝₁ t3) -> (t1 ↝* t3)
| Red_Trans : forall t2, (t1 ↝₁ t2) -> (t2 ↝* t3) -> (t1 ↝* t3)
where "s ↝* t" := (Red s t).

Hint Constructors Red.

Lemma Red_Trans' : forall t1 t2 t3, (t1 ↝* t2) -> (t2 ↝* t3) -> (t1 ↝* t3).
Proof.
  intros t1 t2 t3 H1.
  revert t3.
  induction H1; eauto.
Qed.

Hint Resolve Red_Trans'.

Theorem ChurchRosser1_many (t s1 s2 : Trm) :
  (t ↝₁ s1) -> (t ↝* s2) -> {r : Trm & (s1 ↝* r) & (s2 ↝* r)}.
Proof.
  intros H1 H2.
  assert (G : forall s, (t ↝₁ s) -> {r : Trm & (s1 ↝* r) & (s ↝₁ r)}).
  {  
    intros s G.
    edestruct (ChurchRosser1 _ _ _ G H1); eauto.
  }
  {    
    clear H1.
    induction H2 as [? ? H2|].
    - edestruct G; eauto.
    - apply IHRed.
      intros s H3.
      edestruct G as [s' G1 G2]; [eassumption|].
      edestruct (ChurchRosser1 _ _ _ H3 G2); eauto.
  }
Qed.
  
Theorem ChurchRosser (t s1 s2 : Trm) :
  (t ↝* s1) -> (t ↝* s2) -> {r : Trm & (s1 ↝* r) & (s2 ↝* r)}.
Proof.
  intros H1.
  revert s2.
  induction H1; eauto; intros s2 H2.
  - eapply ChurchRosser1_many; eauto.
  - edestruct ChurchRosser1_many; try eassumption.
    edestruct IHRed; eauto.
Qed.
