Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive form : Type :=
  | atom : Prop -> form
  | conj : form -> form -> form
  | true : form
  | disj : form -> form -> form
  | fals : form
  | impl : form -> form -> form
  .

Fixpoint propify (F : form) : Prop :=
  match F with
  | atom A => A
  | conj F1 F2 => propify F1 /\ propify F2
  | true => True
  | disj F1 F2 => propify F1 \/ propify F2
  | fals => False
  | impl F1 F2 => propify F1 -> propify F2
  end.

Inductive side : Type :=
  | lft : side
  | rgt : side
  .

Definition ctx : Type := list form.

Fixpoint propify_ctx (Sd : side) (G : ctx) : Prop :=
  match G with
  | [] =>
    match Sd with
    | lft => True
    | rgt => False
    end
  | F :: G =>
    let F1 := propify F in
    let F2 := propify_ctx Sd G in
    match Sd with
    | lft => F1 /\ F2
    | rgt => F1 \/ F2
    end
  end.

Inductive seq : Type :=
  | s_neut  : ctx -> ctx -> seq
  | s_foc   : ctx -> side -> form -> ctx -> seq
  .

Fixpoint propify_seq (S : seq) : Prop :=
  match S with
  | s_neut Gx Dx =>
      propify_ctx lft Gx -> propify_ctx rgt Dx
  | s_foc Gx lft F Dx =>
      propify_ctx lft (F :: Gx) -> propify_ctx rgt Dx
  | s_foc Gx rgt F Dx =>
      propify_ctx lft Gx -> propify_ctx rgt (F :: Dx)
  end.

Inductive cert : Type :=
  | c0 : cert
  | c1 : cert -> cert
  | c2 : cert -> cert -> cert
  | ix : nat -> cert
  | dc : side -> nat -> cert -> cert
  .

Fixpoint equate (Gx : ctx) (N : nat) (A : Prop) : Prop :=
  match Gx with
  | [] => False
  | F :: Gx =>
    match N with
    | O =>
      match F with
      | atom B => A = B
      | _ => False
      end
    | S N => equate Gx N A
    end
  end.

Fixpoint get (Gx : ctx) (N : nat) : option form :=
  match Gx with
  | [] => None
  | F :: Gx =>
    match N with
    | O => Some F
    | S N => get Gx N
    end
  end.

Fixpoint check (C : cert) (S : seq) : Prop :=
  match S with
  | s_foc Gx lft F Dx =>
    match F with
    | atom A =>
      match C with
      | ix N => equate Dx N A
      | _ => False
      end
    | conj A B =>
      match C with
      | c1 C => check C (s_neut (B :: A :: Gx) Dx)
      | _ => False
      end
    | true => False
    | disj A B =>
      match C with
      | c2 C1 C2 =>
          check C1 (s_neut (A :: Gx) Dx) /\
          check C2 (s_neut (B :: Gx) Dx)
      | _ => False
      end
    | fals =>
      match C with
      | c0 => True
      | _ => False
      end
    | impl A B =>
      match C with
      | c2 C1 C2 =>
          check C1 (s_neut Gx (A :: Dx)) /\
          check C2 (s_neut (B :: Gx) Dx)
      | _ => False
      end
    end
  | s_foc Gx rgt F Dx =>
    match F with
    | atom A =>
      match C with
      | ix N => equate Gx N A
      | _ => False
      end
    | conj F1 F2 =>
      match C with
      | c2 C1 C2 =>
          check C1 (s_neut Gx (F1 :: Dx)) /\
          check C2 (s_neut Gx (F2 :: Dx))
      | _ => False
      end
    | true =>
      match C with
      | c0 => True
      | _ => False
      end
    | disj F1 F2 =>
      match C with
      | c1 C => check C (s_neut Gx (F1 :: F2 :: Dx))
      | _ => False
      end
    | fals => False
    | impl F1 F2 =>
      match C with
      | c1 C =>
          check C (s_neut (F1 :: Gx) (F2 :: Dx))
      | _ => False
      end
    end
  | s_neut Gx Dx =>
    match C with
    | dc lft N C =>
      match get Gx N with
      | Some F => check C (s_foc Gx lft F Dx)
      | None => False
      end
    | dc rgt N C =>
      match get Dx N with
      | Some F => check C (s_foc Gx rgt F Dx)
      | None => False
      end
    | _ => False
    end
  end.

Theorem test_xm : forall A, check
  (dc rgt 0 (c1 (dc rgt 1 (c1 (dc lft 0 (ix 1))))))
  (s_neut [] [disj (atom A) (impl (atom A) fals)]).
Proof.
intros. simpl. intuition.
Qed.

Lemma eq_left : forall Gx N P,
  equate Gx N P -> propify_ctx lft Gx -> P.
Proof.
induction Gx ; intros ; try destruct H ; destruct N.
* destruct a ; try destruct H ; simpl in H0 ; intuition.
* simpl in H. destruct H0 as [ H1 H2 ].
  exact (IHGx _ _ H H2).
Qed.

Lemma eq_right : forall Gx N P,
  equate Gx N P -> P -> propify_ctx rgt Gx.
Proof.
induction Gx ; intros ; try destruct H ; destruct N.
* destruct a ; try destruct H ; simpl ; intuition.
* simpl in H |- *. right. exact (IHGx _ _ H H0).
Qed.

Lemma get_left : forall N Gx F,
  get Gx N = Some F ->
  propify_ctx lft Gx -> propify F.
Proof.
induction N ; intros ; destruct Gx ; try discriminate H.
* injection H. intros ; subst ;  destruct H0 as [H1 _] ; exact H1.
* destruct H0 as [_ HH] ; exact (IHN _ _ H HH).
Qed.

Lemma get_right : forall N Gx F,
  get Gx N = Some F ->
  propify F -> propify_ctx rgt Gx.
Proof.
induction N ; intros ; destruct Gx ; try discriminate H.
* injection H ; intros ; subst. simpl ; left ; exact H0.
* simpl ; right ; exact (IHN _ _ H H0).
Qed.

(* This is the only classical axiom used, which is a
   propositional version of the independence of premise
   principle. *)
Axiom class : forall (P Q R : Prop), (P -> (Q \/ R)) -> ((P -> Q) \/ R).

Theorem sound : forall C S, check C S -> propify_seq S.
Proof.
induction C as [ | C IH | C1 IH1 C2 IH2 | N C | CSi N C IH ] ;
destruct S as [Gx Dx | Gx Si F Dx] ; intro Hchk ; try destruct Hchk.
* destruct Si ; destruct F ; try destruct Hchk ; simpl ; intuition.
* destruct Si ; destruct F ; try destruct Hchk ;
  specialize (IH _ Hchk) ; simpl in IH |- * ; try intuition.
  apply class ; intuition.
* destruct Si ; destruct F ; try destruct Hchk ;
  specialize (IH1 _ H) ; specialize (IH2 _ H0) ;
  simpl in IH1, IH2 |- * ; intuition.
* destruct Si ; destruct F ; try destruct Hchk ; simpl in Hchk |- *.
   - intros [Hp _]. exact (eq_right Dx N P Hchk Hp).
   - intros HGx ; left ; exact (eq_left Gx N P Hchk HGx).
* destruct CSi ; try destruct Hchk ; simpl in Hchk.
  - destruct (get Gx N) eqn:Heq ; [ | intuition ].
    specialize (IH _ Hchk). simpl in IH |- *. intros.
    apply IH ; split ; [ exact (get_left _ _ _ Heq H) | intuition ].
  - destruct (get Dx N) eqn:Heq ; [ | intuition ].
    specialize (IH _ Hchk) ; simpl in IH |- * ; intros.
    specialize (IH H) ; destruct IH as [Hf | HDx] ; [ | intuition ].
    exact (get_right _ _ _ Heq Hf).
* destruct Si ; try destruct Hchk ; destruct F ;
  simpl in Hchk ; intuition.
Qed.

Fixpoint check2 (C : cert) (S : seq) : Prop :=
  match S with
  | s_foc Gx lft F Dx =>
    match C, F with
    | ix N, atom A => equate Dx N A
    | c1 C, conj A B => check2 C (s_neut (B :: A :: Gx) Dx)
    | _, true => False
    | c2 C1 C2, disj A B =>
        check2 C1 (s_neut (A :: Gx) Dx) /\
        check2 C2 (s_neut (B :: Gx) Dx)
    | c0, fals => True
    | c2 C1 C2, impl A B =>
        check2 C1 (s_neut Gx (A :: Dx)) /\
        check2 C2 (s_neut (B :: Gx) Dx)
    | _, _ => False
    end
  | s_foc Gx rgt F Dx =>
    match F with
    | atom A =>
      match C with
      | ix N => equate Gx N A
      | _ => False
      end
    | conj F1 F2 =>
      match C with
      | c2 C1 C2 =>
          check2 C1 (s_neut Gx (F1 :: Dx)) /\
          check2 C2 (s_neut Gx (F2 :: Dx))
      | _ => False
      end
    | true =>
      match C with
      | c0 => True
      | _ => False
      end
    | disj F1 F2 =>
      match C with
      | c1 C => check2 C (s_neut Gx (F1 :: F2 :: Dx))
      | _ => False
      end
    | fals => False
    | impl F1 F2 =>
      match C with
      | c1 C =>
          check2 C (s_neut (F1 :: Gx) (F2 :: Dx))
      | _ => False
      end
    end
  | s_neut Gx Dx =>
    match C with
    | dc lft N C =>
      match get Gx N with
      | Some F => check2 C (s_foc Gx lft F Dx)
      | None => False
      end
    | dc rgt N C =>
      match get Dx N with
      | Some F => check2 C (s_foc Gx rgt F Dx)
      | None => False
      end
    | _ => False
    end
  end.

Theorem sound2 : forall C S, check2 C S -> propify_seq S.
Proof.
induction C as [ | C IH | C1 IH1 C2 IH2 | N C | CSi N C IH ] ;
destruct S as [Gx Dx | Gx Si F Dx] ; intro Hchk ;
try destruct F ; try destruct Si ; try destruct Hchk ; try firstorder.

* destruct Si ; destruct F ; try destruct Hchk ; simpl ; intuition.
* destruct Si ; destruct F ; try destruct Hchk ;
  specialize (IH _ Hchk) ; simpl in IH |- * ; try intuition.
  apply class ; intuition.
* destruct Si ; destruct F ; try destruct Hchk ;
  specialize (IH1 _ H) ; specialize (IH2 _ H0) ;
  simpl in IH1, IH2 |- * ; intuition.
* destruct Si ; destruct F ; try destruct Hchk ; simpl in Hchk |- *.
   - intros [Hp _]. exact (eq_right Dx N P Hchk Hp).
   - intros HGx ; left ; exact (eq_left Gx N P Hchk HGx).
* destruct CSi ; try destruct Hchk ; simpl in Hchk.
  - destruct (get Gx N) eqn:Heq ; [ | intuition ].
    specialize (IH _ Hchk). simpl in IH |- *. intros.
    apply IH ; split ; [ exact (get_left _ _ _ Heq H) | intuition ].
  - destruct (get Dx N) eqn:Heq ; [ | intuition ].
    specialize (IH _ Hchk) ; simpl in IH |- * ; intros.
    specialize (IH H) ; destruct IH as [Hf | HDx] ; [ | intuition ].
    exact (get_right _ _ _ Heq Hf).
* destruct Si ; try destruct Hchk ; destruct F ;
  simpl in Hchk ; intuition.
Qed.
