Require Import Coq.Arith.Peano_dec.

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

Reserved Notation "[ Γ ] ⊢ t ::: T" (at level 100, no associativity).

(** Typing relation *)
Inductive Typed : Context -> Trm -> Typ -> Prop :=
| Tpd_Un : forall (Γ: Context), [Γ] ⊢ un ::: Un
| Tpd_Var_O : forall (T : Typ) (Γ: Context), [T, Γ] ⊢ 𝔳(O) ::: T
| Tpd_Var_S : forall (n : nat) (T : Typ) (Γ: Context),
    ([Γ] ⊢ 𝔳(n) ::: T) -> [T, Γ] ⊢ 𝔳(S n) ::: T
| Tpd_Func : forall (Γ : Context) (t : Trm) (T T' : Typ),
    ([T, Γ] ⊢ t ::: T') -> ([Γ] ⊢ (λ t) ::: (T —≻ T'))
| Tpd_App : forall (Γ : Context) (t t' : Trm) (T T' : Typ),
    ([Γ] ⊢ t ::: (T —≻ T')) -> ([Γ] ⊢ t' ::: T) -> ([Γ] ⊢ (t · t') ::: T')
where "[ Γ ] ⊢ t ::: T " := (Typed Γ t T).

(** substitution *)
Fixpoint subst (t : Trm) (x : nat) (m : Trm) : Trm :=
  match t with
  | un => un
  | 𝔳(y) =>
    match eq_nat_dec x y with
    | left _ => m
    | _ => 𝔳(y)
    end
  | λ f => subst f (S x) m
  | t1 · t2 => (subst t1 x m) · (subst t2 x m)
  end
.

Notation "t [ x // m ]" := (subst t x m) (at level 100, no associativity).

Reserved Notation "s ↝ t" (at level 100, no associativity).

Inductive Red : Trm -> Trm -> Prop :=
| Beta : forall (t t': Trm), ((λ t) · t') ↝ (t [O // t'])
where "s ↝ t" := (Red s t).