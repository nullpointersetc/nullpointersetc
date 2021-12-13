(**
*** To use this file: 
******* coqtop -l Hardegree_5_22
*** or
******* coqtop -lv Hardegree_5_22
***
*** This is an example of exercises from Gary Hardegree's textbook,
*** "Symbolic Logic: A First Course" as published at
*** <http://courses.umass.edu/phil110-gmh/MAIN/IHome-5.htm>
*** as of December 8th 2021, done as a Coq session.
*** The exercises are taken from section 5.22 of the textbook.
**)

Section Hardegree_5_22_1_and_2.

(** Example Exercise_1 is equivalent to this
*** symbolic proof which is mostly in Hardegree's notation.
***
*** (1) P           Pr
*** (2) P → Q       Pr
*** (3) Q → R       Pr
*** (4) R → S       Pr
*** (5) SHOW: S     DD
*** (6) |   Q       2,1,MPP
*** (7) |   R       3,6,MPP
*** (8) |   S       4,7,MPP,QED
***
*** Note: "Pr" indicates a Premise. "DD" indicates Direct Derivation.
*** "MPP" indicates Modus Ponendo Ponens (Hardegree would use →O instead.)
*** I am indicating the end of proof with "QED" (Quod Erat Demonstrandum).
**)

Example Exercise_1
        (P : Prop) (Q : Prop)
        (R : Prop) (S : Prop)
        (Pr_1: P)
        (Pr_2: P -> Q)
        (Pr_3: Q -> R)
        (Pr_4: R -> S) : S.
Proof.
        assert (MPP_6 := Pr_2 (Pr_1) : Q).
        assert (MPP_7 := Pr_3 (MPP_6) : R).
        assert (MPP_8 := Pr_4 (MPP_7) : S).
        exact MPP_8.
Qed.

(** Example Exercise_2 is equivalent to this
*** symbolic proof which is mostly in Hardegree's notation.
***
*** (1) P → Q       Pr
*** (2) Q → R       Pr
*** (3) R → S       Pr
*** (4) ~ S         Pr
*** (5) SHOW: ~ P   DD
*** (6) |   ~ R     3,4,MTT
*** (7) |   ~ Q     2,6,MTT
*** (8) |   ~ P     1,7,MTT,QED
***
*** Note: "MPP" indicates Modus Tollendo Tollens
*** (Hardegree would use →O instead.)
**)

Example Exercise_2
        (P : Prop) (Q : Prop)
        (R : Prop) (S : Prop)
        (Pr_1: P -> Q)
        (Pr_2: Q -> R)
        (Pr_3: R -> S)
        (Pr_4: not S) : not P.
Proof.
        assert (MTT_6 := (fun (Rx : R) => Pr_4 (Pr_3 (Rx))) : not R).

        assert (MTT_7 := (fun (Qx : Q) => MTT_6 (Pr_2 (Qx))) : not Q).

        assert (MTT_8 := (fun (Px : P) => MTT_7 (Pr_1 (Px))) : not P).

        exact MTT_8.
Qed.

End Hardegree_5_22_1_and_2.

(** To simplify further proofs using Modus Tollendo Tollens,
*** we can define a function that returns a "not S"
*** given an "S implies D" and a "not D" (in that order). **)

Section Modus_tollendo_tollens.

Definition Mtt {S : Prop} {D : Prop}
        (S_implies_D : S -> D)
        (not_D : not D) : not S
        := fun (Sx : S) => not_D (S_implies_D (Sx)).

End Modus_tollendo_tollens.

Section Hardegree_5_22_2_and_3.

Example Exercise_2_again
        (P : Prop) (Q : Prop)
        (R : Prop) (S : Prop)
        (Pr_1: P -> Q)
        (Pr_2: Q -> R)
        (Pr_3: R -> S)
        (Pr_4: not S) : not P.
Proof.
        assert (MTT_6 := Mtt (Pr_3) (Pr_4) : not R).

        assert (MTT_7 := Mtt (Pr_2) (MTT_6) : not Q).

        assert (MTT_8 := Mtt (Pr_1) (MTT_7) : not P).

        exact MTT_8.
Qed.

Example Exercise_3
  (P:Prop) (Q:Prop) (R:Prop)
  (Pr_1: or (not(P)) (Q))
  (Pr_2: not (Q))
  (Pr_3: or (P) (R)) : R.
Proof.
  assert (MTPs_5 := match Pr_1
    return not P
    with or_introl not_P => not_P
    | or_intror Qx =>
      (match Pr_2 (Qx) return not P with end)
    end).

  assert (MTPd_6 := match Pr_3
    return R
    with or_introl Px =>
      (match MTPs_5 (Px) return R with end)
    | or_intror Rx => Rx
    end).

  exact MTPd_6.
Qed.

End Hardegree_5_22_2_and_3.

Section Modus_tollendo_ponens_sinistrum.

Definition MTPs {S : Prop} {D : Prop}
        (Sx_or_Dx : or S D)
        (not_Dx   : not D) : S
        := match Sx_or_Dx return S
        with or_introl Sx =>
                Sx
        | or_intror Dx =>
                (match not_Dx (Dx)
                return S with end)
        end.

End Modus_tollendo_ponens_sinistrum.

Section Modus_tollendo_ponens_dextrum.

Definition MTPd {S : Prop} {D : Prop}
        (Sx_or_Dx : or S D)
        (not_Sx   : not S) : D
        := match Sx_or_Dx return D
        with or_introl Sx =>
                (match not_Sx (Sx)
                return D with end)
        | or_intror Dx =>
                Dx
        end.

End Modus_tollendo_ponens_dextrum.


Section Hardegree_5_22_3.

Example Exercise_3_again
  (P:Prop) (Q:Prop) (R:Prop)
  (Pr_1: or (not(P)) (Q))
  (Pr_2: not (Q))
  (Pr_3: or (P) (R)) : R.
Proof.
  assert (MTPs_5 := MTPs (Pr_1) (Pr_2) : not P).
  assert (MTPd_6 := MTPd (Pr_3) (MTPs_5) : R).
  exact MTPd_6.
Qed.

End Hardegree_5_22_3.
