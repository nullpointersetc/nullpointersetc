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

Module Hardegree_5_22.

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

