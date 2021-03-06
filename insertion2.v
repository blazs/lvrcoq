Require Import List.
Require Import ZArith.
Require Import Sorting. (** Roba od Bauerja. *)
Require Import Recdef. (** To potrebujemo za definicijo s [Function]. *)
Require Import Bool.


Fixpoint vstavi (x : Z) (l : list Z) :=
  match l with
    | nil => x::nil
    | y::l' => if (Z.leb x y) then x::l else y:: (vstavi x l') 
  end.

Fixpoint insertion( l : list Z) :=
   match l with
    | nil => nil
    | x::l' =>
       let l'' := insertion l' in 
          vstavi x l''
   end.

(** Ce je seznam x::l urejen, potem je urejen tudi njegov rep l. *)
Lemma urejen_tail (x : Z) (l : list Z) :
  urejen(x::l) -> urejen(l).
Proof.
  induction l;auto.
  intros[? ?].
  auto.
Qed.

Eval compute in insertion (1::4::3::6::2::8::7::nil)%Z.

(** Vstavi ohranja urejenost: ce je seznam l urejen, potem je urejen tudi 
   seznam, ki ga dobimo kot rezultat klica vstavi a l, za nek element a. *)
Lemma vstaviP: forall a : Z, forall l:list Z,
  urejen (l) -> urejen(vstavi a l).
Proof.
  induction l.
  -simpl ; auto.
  -intros.
   simpl.
   case_eq (Z.leb a a0).
   intros G.
     + simpl.
       destruct l.
         *firstorder.
           apply Zle_is_le_bool.
           assumption.
          *split.
           apply Zle_is_le_bool.
           assumption.
           split.
           unfold urejen in H.
           destruct H.
             assumption.

             apply urejen_tail in H.
             assumption.
     +intro.
      simpl.
      destruct l;simpl.
        *firstorder.
          SearchAbout(?x < ?y -> ?x <= ?y)%Z.
          apply Z.lt_le_incl.
          SearchAbout(?x <=? ?y)%Z.
          assert (G := Zle_cases a a0).
          rewrite H0 in G.
          firstorder.
        *apply Z.leb_gt in H0.
          case_eq(Z.leb a z).
            intro.
            firstorder.
            apply Z.leb_le in H1.
            auto.
            intros.
            firstorder.
            replace (z :: vstavi a l) with (vstavi a (z :: l)).
              auto.
              simpl.
              rewrite H1.
              reflexivity.
Qed.

(** Insertion sort na vhood vzame seznam in vrne nek urejen seznam. *)
Lemma pravilnost1 (l : list Z):
  urejen (insertion l).
Proof.
induction l.
    -simpl.
     auto.
    -simpl.
    apply vstaviP.
    auto.
Qed.

(** Ce v seznam l vstavim element a, se stevilo pojavitev poveca za 1. *)
Lemma pojavi_vstavi(a : Z)(l : list Z):
    S (pojavi a ( l)) = pojavi a (vstavi a ( l)).
Proof.
    induction l.
      -simpl.
      SearchAbout(Z.eqb ?a ?a).
      rewrite Z.eqb_refl.
      auto.
      -simpl. 
       case_eq(Z.leb a a0).
         *intros.
          simpl.
          rewrite Z.eqb_refl.
          auto.
         *intros.
          simpl.
          case(Z.eqb a a0).
            +auto.
            +apply IHl.
Qed.

Lemma pojavi_vstavi2(a b : Z) (l : list Z):
    ((a =? b)%Z = false) -> pojavi a l = pojavi a (vstavi b l).
Proof.
    induction l.
    + intro. simpl. rewrite H. auto.
    + intro. simpl. case_eq(a =? a0)%Z.
      - intro.
        case_eq(b <=? a0)%Z.
          intro. simpl. rewrite H. rewrite H0. auto.
          intro. simpl. rewrite IHl. rewrite H0. auto. firstorder.
      - intro.
        case_eq(b <=? a0)%Z. intro. simpl. rewrite H. rewrite H0. auto.
        intro. simpl. rewrite IHl. rewrite H0. auto. firstorder.
Qed.

Lemma ohranja_elemente(l : list Z):
    l ~~ insertion l.
Proof.
    induction l.
    + intro. auto.
    + intro. simpl.
      SearchAbout(?x = ?a).
      case_eq (Z.eqb x a).
      - intro. rewrite IHl. rewrite Z.eqb_eq in H.
        simpl. rewrite H. (* rewrite (vstavi a (insertion l)). *)
        apply pojavi_vstavi.
      - intro. rewrite IHl. rewrite Z.eqb_neq in H.
        simpl. apply pojavi_vstavi2. firstorder. auto. apply Z.eqb_neq. apply H. 
Qed.

(** Insertion sort deluje pravilno. *)
Theorem pravilnost_insertion_sort (l : list Z):
	urejen (insertion l) /\ l ~~ insertion l.
Proof.
	split;
        [apply pravilnost1 | apply ohranja_elemente].
Qed.
     

