Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Import ListNotations.

Module Type LKF_Params.

  (* Predicate symbols *)
  Parameter Prd     : Set.
  Parameter Prd_eqb : Prd -> Prd -> bool.

  (* Constants *)
  Parameter Fun     : Set.
  Parameter Fun_eqb : Fun -> Fun -> bool.

End LKF_Params.

Module LKF (Params : LKF_Params).

  Import Params.

  (* Terms *)
  Inductive Tm : Set :=
  | Var : nat -> Tm
  | App : Fun -> list Tm -> Tm
  .

  Fixpoint Tm_eqb (t1 t2 : Tm) : bool :=
    match t1, t2 with
    | Var j, Var k => Nat.eqb j k
    | App f1 ts1, App f2 ts2 =>
      let fix args ts1 ts2 :=
          match ts1, ts2 with
          | [], [] => true
          | t1 :: ts1, t2 :: ts2 =>
              andb (Tm_eqb t1 t2) (args ts1 ts2)
          | _, _ => false
          end
      in andb (Fun_eqb f1 f2) (args ts1 ts2)
    | _, _ => false
    end.

  Fixpoint repl_tm (k : nat) (x : Tm) (t : Tm) : Tm :=
    match t with
    | Var j => if Nat.eqb k j then x else t
    | App f ts => App f (map (repl_tm k x) ts)
    end.

  (* Polarity *)
  Inductive Pol : Set :=
  | Positive : Pol
  | Negative : Pol
  .

  (* Polarized formulas *)
  Inductive Form : Set :=
  | Atom  : Pol -> Prd -> list Tm -> Form
  | And   : Pol -> Form -> Form -> Form
  | True  : Pol -> Form
  | Or    : Pol -> Form -> Form -> Form
  | False : Pol -> Form
  | Quant : Pol -> (Tm -> Form) -> Form
  .

  Fixpoint repl_form (k : nat) (x : Tm) (f : Form) : Form :=
    match f with
    | Atom p a ts => Atom p a (map (repl_tm k x) ts)
    | And p a b   => And p (repl_form k x a) (repl_form k x b)
    | True p      => True p
    | Or p a b    => Or p (repl_form k x a) (repl_form k x b)
    | False p     => False p
    | Quant p a   => Quant p (fun y => repl_form k x (a y))
    end.

  Fixpoint get_pol (f : Form) : Pol :=
    match f with
    | Atom p _ _  => p
    | And p _ _ => p
    | True p    => p
    | Or p _ _  => p
    | False p   => p
    | Quant p _ => p
    end.

  (* De Morgan duality *)

  Fixpoint dual_pol (p : Pol) : Pol :=
    match p with
    | Positive => Negative
    | Negative => Positive
    end.

  Fixpoint dual (f : Form) : Form :=
    match f with
    | Atom p a ts => Atom (dual_pol p) a ts
    | And p f1 f2 => Or (dual_pol p) (dual f1) (dual f2)
    | True p      => False (dual_pol p)
    | Or p f1 f2  => And (dual_pol p) (dual f1) (dual f2)
    | False p     => True (dual_pol p)
    | Quant p f   => Quant (dual_pol p) (fun t => dual (f t))
    end.

  (* Sequents *)

  Inductive SeqKind : Set := Unf | Foc.
  Inductive Sequent : Set :=
  | Seq : SeqKind -> nat -> list Form -> list Form -> Sequent.

  (* Certificates *)

  Inductive Choice : Set :=
  | ChLeft : Choice
  | ChRight : Choice
  .

  Inductive Cert : Set :=
  | C0 : Cert                         (* nullary *)
  | C1 : Cert -> Cert                 (* unary *)
  | C2 : Cert -> Cert -> Cert         (* binary *)
  | Ch : Choice -> Cert -> Cert       (* choice *)
  | Cx : nat -> Cert                  (* index *)
  | Cd : nat -> Cert -> Cert          (* decision *)
  | Ce : (Tm -> Cert) -> Cert         (* eigen *)
  | Cw : Tm -> Cert -> Cert           (* witness *)
  | Ct : Form -> Cert -> Cert -> Cert (* cut *)
  .

  Fixpoint cert_size (c : Cert) : nat :=
    match c with
    | C0 => O
    | C1 c => cert_size c + 1
    | C2 c1 c2 => cert_size c1 + cert_size c2 + 1
    | Ch _ c1 => cert_size c1 + 1
    | Cx _ => O
    | Cd _ c => cert_size c + 1
    | Ce cf => cert_size (cf (Var O)) + 1
    | Cw _ c => cert_size c + 1
    | Ct _ c1 c2 => cert_size c1 + cert_size c2 + 1
    end.

  (* Checking *)

  Fixpoint get (Gx : list Form) (n : nat) :=
    match Gx, n with
    | (F :: _), O => Some F
    | (_ :: Gx), (S n) => get Gx n
    | _, _ => None
    end.

  Fixpoint atom_check (Gx : list Form) (n : nat) (b : Prd) (bts : list Tm) : Prop :=
    match Gx, n with
    | (Atom Negative a ats :: _), O =>
        let fix args ts1 ts2 : Prop :=
            match ts1, ts2 with
            | [], [] => Logic.True
            | t1 :: ts1, t2 :: ts2 =>
                Is_true (Tm_eqb t1 t2) /\
                args ts1 ts2
            | _, _ => Logic.False
            end
        in Is_true (Prd_eqb a b) /\ args ats bts
    | (_ :: Gx), (S n) => atom_check Gx n b bts
    | _, _ => Logic.False
    end.

  Fixpoint check (cc : Cert) (sq : Sequent) : Prop :=
    match sq with
    | Seq Foc Si Gx [F] =>
      match cc, F with
      (* init *)
      | Cx n, Atom Positive a ts =>
        atom_check Gx n a ts
      (* top+ *)
      | C0, True Positive =>
        Logic.True
      (* and+ *)
      | C2 cca ccb, And Positive A B =>
        check cca (Seq Foc Si Gx [A]) /\ check ccb (Seq Foc Si Gx [B])
      (* or+1 *)
      | Ch ChLeft cc, Or Positive A _ =>
        check cc (Seq Foc Si Gx [A])
      (* or+2 *)
      | Ch ChRight cc, Or Positive _ B =>
        check cc (Seq Foc Si Gx [B])
      (* false+ *)
      | _, False Positive => Logic.False
      (* exists *)
      | Cw t cc, Quant Pos A =>
        check cc (Seq Foc Si Gx [A t])
      (* release *)
      | C1 cc, F =>
        check cc (Seq Unf Si Gx [F])
      | _, _ =>
        Logic.False
      end
    | Seq Foc _ _ _ => Logic.False
    | Seq Unf Si Gx nil =>
      match cc with
      (* decide *)
      | Cd n cc =>
        match get Gx n with
        | Some F => check cc (Seq Foc Si Gx [F])
        | None => Logic.False
        end
      (* cut *)
      | Ct F cc1 cc2 =>
        check cc1 (Seq Unf Si Gx [F]) /\
        check cc2 (Seq Unf Si Gx [dual F])
      | _ => Logic.False
      end
    | Seq Unf Si Gx (F :: Dx) =>
      match cc, F with
      (* store *)
      | C1 cc, ( Atom _ _ _
               | And Positive _ _
               | True Positive
               | Or Positive _ _
               | False Positive
               | Quant Positive _ ) => check cc (Seq Unf Si (F :: Gx) Dx)
      (* top- *)
      | C0, True Negative => Logic.True
      (* and- *)
      | C2 cca ccb, And Negative A B =>
        check cca (Seq Unf Si Gx (A :: Dx)) /\
        check ccb (Seq Unf Si Gx (B :: Dx))
      (* bot- *)
      | C1 cc, False Negative =>
        check cc (Seq Unf Si Gx Dx)
      (* or- *)
      | C1 cc, Or Negative A B =>
        check cc (Seq Unf Si Gx (A :: B :: Dx))
      (* forall *)
      | Ce cc, Quant Negative A =>
        check (cc (Var Si)) (Seq Unf (S Si) Gx (A (Var Si) :: Dx))
      | _, _ => Logic.False
      end
    end.

End LKF.

Module TestParams <: LKF_Params.
  Definition Fun := nat.
  Definition Fun_eqb := Nat.eqb.

  Definition Prd := nat.
  Definition Prd_eqb := Nat.eqb.
End TestParams.

Module LKF_Test := LKF (TestParams).
Import TestParams LKF_Test.

Definition d (t : Tm) : Form := Atom Positive O [t].

Definition drinker1 :=
  Quant
    Positive
    (fun x =>
       Quant
         Negative
         (fun y =>
            Or Negative (dual (d x)) (d y))).

Parameter c : Tm.

Definition drinker_cert1 : Cert :=
  (C1                           (* store *)
  (Cd O                         (* decide on drinker *)
  (Cw c                         (* exists *)
  (C1                           (* release *)
  (Ce (fun y =>                 (* forall *)
  (C1 (C1 (C1                   (* or-, store, store *)
  (Cd 2                         (* decide on drinker *)
  (Cw y                         (* exists *)
  (C1                           (* release *)
  (Ce (fun _ =>                 (* forall *)
  (C1 (C1 (C1                   (* or-, store, store *)
  (Cd 2                         (* decide on d(y) *)
  (Cx 1                         (* init *)
  )))))))))))))))))))
.

Theorem dr_check1 : check drinker_cert1 (Seq Unf O [] [drinker1]).
Proof.
simpl ; auto.
Qed.

(* TODO: try with or+ in drinker *)