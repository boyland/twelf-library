%{%
#ifndef WORLDS
#define WORLDS /* nothing */
#endif
/* We require MULN-right-distributes-over-ADDN and create the rest */
/* If ADD is not total, we require MULN-right-factors-over-ADDN too */
%}%

%theorem MULN-right-distributes-over-ADDN* :
	forall* {X1} {X2} {X3} {X4} {X5} {X6} {X7}
        forall {A12:ADDN X1 X2 X3} {M34:MULN X3 X4 X7}
               {M14:MULN X1 X4 X5} {M24:MULN X2 X4 X6}
        exists {A56:ADDN X5 X6 X7}
	true.

- : MULN-right-distributes-over-ADDN* ADD(X1,X2)=X3 MUL(X3,X4)=X7 MUL(X1,X4)=X5 MUL(X2,X4)=X6 ADD(X5,X6)=X7
    <- MULN-right-distributes-over-ADDN ADD(X1,X2)=X3 MUL(X3,X4)=X7 Y5 Y6
                                      MUL(X1,X4)=Y5 MUL(X2,X4)=Y6 ADD(Y5,Y6)=X7
    <- MULN-deterministic MUL(X1,X4)=Y5 MUL(X1,X4)=X5 EQ/ EQ/ Y5=X5
    <- MULN-deterministic MUL(X2,X4)=Y6 MUL(X2,X4)=X6 EQ/ EQ/ Y6=X6
    <- ADDN-respects-EQ ADD(Y5,Y6)=X7 Y5=X5 Y6=X6 EQ/ ADD(X5,X6)=X7.

%worlds (WORLDS) (MULN-right-distributes-over-ADDN* ADD(X1,X2)=X3 MUL(X3,X4)=X7 MUL(X1,X4)=X5 MUL(X2,X4)=X6
                                      %{=>}% ADD(X5,X6)=X7).
%total {} (MULN-right-distributes-over-ADDN* _ _ _ _ _).

%{%
#ifdef MUL_COMMUTATIVE
%}%

%theorem MULN-left-distributes-over-ADDN* :
	forall* {X1} {X2} {X3} {X4} {X5} {X6} {X7}
        forall {A12:ADDN X2 X4 X6} {M34:MULN X1 X6 X7}
               {M14:MULN X1 X2 X3} {M24:MULN X1 X4 X5}
        exists {A56:ADDN X3 X5 X7}
	true.

- : MULN-left-distributes-over-ADDN* ADD(X2,X4)=X6 MUL(X1,X6)=X7 MUL(X1,X2)=X3 MUL(X1,X4)=X5 ADD(X3,X5)=X7
    <- MULN-commutative MUL(X1,X6)=X7 MUL(X6,X1)=X7
    <- MULN-commutative MUL(X1,X2)=X3 MUL(X2,X1)=X3
    <- MULN-commutative MUL(X1,X4)=X5 MUL(X4,X1)=X5
    <- MULN-right-distributes-over-ADDN* ADD(X2,X4)=X6 MUL(X6,X1)=X7 MUL(X2,X1)=X3 MUL(X4,X1)=X5
                                       ADD(X3,X5)=X7.

%worlds (WORLDS) (MULN-left-distributes-over-ADDN* ADD(X2,X4)=X6 MUL(X1,X6)=X7 MUL(X1,X2)=X3 MUL(X1,X4)=X5
                                    %{=>}% ADD(X3,X5)=X7).
%total {} (MULN-left-distributes-over-ADDN* _ _ _ _ _).


%theorem MULN-left-distributes-over-ADDN :
	forall* {X1} {X2} {X4} {X6} {X7}
        forall {A12:ADDN X2 X4 X6} {M34:MULN X1 X6 X7}
        exists {X3} {X5} {M14:MULN X1 X2 X3} {M24:MULN X1 X4 X5}
               {A56:ADDN X3 X5 X7}
	true.

- : MULN-left-distributes-over-ADDN ADD(X2,X4)=X6 MUL(X1,X6)=X7 
                                  X3 X5 MUL(X1,X2)=X3 MUL(X1,X4)=X5 ADD(X3,X5)=X7
    <- MULN-total MUL(X1,X2)=X3
    <- MULN-total MUL(X1,X4)=X5
    <- MULN-left-distributes-over-ADDN* ADD(X2,X4)=X6 MUL(X1,X6)=X7 MUL(X1,X2)=X3 MUL(X1,X4)=X5
                                      ADD(X3,X5)=X7.

%worlds (WORLDS) (MULN-left-distributes-over-ADDN ADD(X2,X4)=X6 MUL(X1,X6)=X7 
                                   %{=>}% X3 X5 MUL(X1,X2)=X3 MUL(X1,X4)=X5 ADD(X3,X5)=X7).
%total {} (MULN-left-distributes-over-ADDN _ _ _ _ _ _ _).

%{%
#endif

#ifdef ADD_TOTAL
%}%

%theorem MULN-right-factors-over-ADDN :
	forall* {X1} {X2} {X4} {X5} {X6} {X7}
        forall {M14:MULN X1 X4 X5} {M24:MULN X2 X4 X6} {A56:ADDN X5 X6 X7}
        exists {X3} {A12:ADDN X1 X2 X3} {M34:MULN X3 X4 X7}
	true.
- : MULN-right-factors-over-ADDN MUL(X1,X4)=X5 MUL(X2,X4)=X6 ADD(X5,X6)=X7 X3 ADD(X1,X2)=X3 MUL(X3,X4)=X7
    <- ADDN-total ADD(X1,X2)=X3
    <- MULN-total MUL(X3,X4)=Y7
    <- MULN-right-distributes-over-ADDN* ADD(X1,X2)=X3 MUL(X3,X4)=Y7 MUL(X1,X4)=X5 MUL(X2,X4)=X6 
                                       ADD(X5,X6)=Y7
    <- ADDN-deterministic ADD(X5,X6)=Y7 ADD(X5,X6)=X7 EQ/ EQ/ Y7=X7
    <- MULN-respects-EQ MUL(X3,X4)=Y7 EQ/ EQ/ Y7=X7 MUL(X3,X4)=X7.

%worlds (WORLDS) (MULN-right-factors-over-ADDN MUL(X1,X4)=X5 MUL(X2,X4)=X6 ADD(X5,X6)=X7
                                %{=>}% X3 ADD(X1,X2)=X3 MUL(X3,X4)=X7 ).
%total {} (MULN-right-factors-over-ADDN _ _ _ _ _ _).

%{%
#define MUL_RIGHT_FACTORS 1
#endif
%}%

%theorem MULN-right-factors-over-ADDN* :
	forall* {X1} {X2} {X3} {X4} {X5} {X6} {X7}
        forall {M14:MULN X1 X4 X5} {M24:MULN X2 X4 X6} {A56:ADDN X5 X6 X7}
               {A12:ADDN X1 X2 X3} 
        exists {M34:MULN X3 X4 X7}
	true.

- : MULN-right-factors-over-ADDN* MUL(X1,X4)=X5 MUL(X2,X4)=X6 ADD(X5,X6)=X7 ADD(X1,X2)=X3 MUL(X3,X4)=X7
    <- MULN-total MUL(X3,X4)=Y7
    <- MULN-right-distributes-over-ADDN* ADD(X1,X2)=X3 MUL(X3,X4)=Y7 MUL(X1,X4)=X5 MUL(X2,X4)=X6 
                                       ADD(X5,X6)=Y7
    <- ADDN-deterministic ADD(X5,X6)=Y7 ADD(X5,X6)=X7 EQ/ EQ/ Y7=X7
    <- MULN-respects-EQ MUL(X3,X4)=Y7 EQ/ EQ/ Y7=X7 MUL(X3,X4)=X7.

%worlds (WORLDS) (MULN-right-factors-over-ADDN* MUL(X1,X4)=X5 MUL(X2,X4)=X6 ADD(X5,X6)=X7 ADD(X1,X2)=X3
                                 %{=>}% MUL(X3,X4)=X7 ).
%total {} (MULN-right-factors-over-ADDN* _ _ _ _ _).

%{%
#ifdef MUL_RIGHT_FACTORS
#ifdef MUL_COMMUTATIVE
%}%

%theorem MULN-left-factors-over-ADDN :
	forall* {X1} {X2} {X3} {X4} {X5} {X7}
	forall {M12:MULN X1 X2 X3} {M14:MULN X1 X4 X5} {A35:ADDN X3 X5 X7}
        exists {X6} {A24:ADDN X2 X4 X6} {M16:MULN X1 X6 X7}
        true.

- : MULN-left-factors-over-ADDN MUL(X1,X2)=X3 MUL(X1,X4)=X5 ADD(X3,X5)=X7 X6 ADD(X2,X4)=X6 MUL(X1,X6)=X7
    <- MULN-commutative MUL(X1,X2)=X3 MUL(X2,X1)=X3
    <- MULN-commutative MUL(X1,X4)=X5 MUL(X4,X1)=X5
    <- MULN-right-factors-over-ADDN MUL(X2,X1)=X3 MUL(X4,X1)=X5 ADD(X3,X5)=X7 X6 ADD(X2,X4)=X6 MUL(X6,X1)=X7
    <- MULN-commutative MUL(X6,X1)=X7 MUL(X1,X6)=X7.

%worlds (WORLDS) (MULN-left-factors-over-ADDN MUL(X1,X2)=X3 MUL(X1,X4)=X5 ADD(X3,X5)=X7
                               %{=>}% X6 ADD(X2,X4)=X6 MUL(X1,X6)=X7).
%total {} (MULN-left-factors-over-ADDN _ _ _ _ _ _).

%{%
#endif
#undef MUL_RIGHT_FACTORS
#endif

#ifdef MUL_COMMUTATIVE
%}%

%theorem MULN-left-factors-over-ADDN* :
	forall* {X1} {X2} {X3} {X4} {X5} {X6} {X7}
	forall {M12:MULN X1 X2 X3} {M14:MULN X1 X4 X5} 
               {A35:ADDN X3 X5 X7} {A24:ADDN X2 X4 X6} 
        exists {M16:MULN X1 X6 X7}
        true.

- : MULN-left-factors-over-ADDN* MUL(X1,X2)=X3 MUL(X1,X4)=X5 ADD(X3,X5)=X7 ADD(X2,X4)=X6 
                               MUL(X1,X6)=X7
    <- MULN-total MUL(X1,X6)=Y7
    <- MULN-left-distributes-over-ADDN* ADD(X2,X4)=X6 MUL(X1,X6)=Y7 MUL(X1,X2)=X3 MUL(X1,X4)=X5
                                      ADD(X3,X5)=Y7
    <- ADDN-deterministic ADD(X3,X5)=Y7 ADD(X3,X5)=X7 EQ/ EQ/ Y7=X7
    <- MULN-respects-EQ MUL(X1,X6)=Y7 EQ/ EQ/ Y7=X7 MUL(X1,X6)=X7.

%worlds (WORLDS) (MULN-left-factors-over-ADDN* MUL(X1,X2)=X3 MUL(X1,X4)=X5 ADD(X3,X5)=X7 ADD(X2,X4)=X6 
                               %{=>}% MUL(X1,X6)=X7).
%total {} (MULN-left-factors-over-ADDN* _ _ _ _ _).

%{%
#endif
%}%
