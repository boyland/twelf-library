
%theorem MULN-right-distributes-over-IADDN :
	forall* {X1} {X2} {X3} {X4} {X7}
        forall {S12:IADDN X1 X2 X3} {M34:MULN X3 X4 X7}
        exists {X5} {X6} {M14:MULN X1 X4 X5} {M24:MULN X2 X4 X6}
               {S56:IADDN X5 X6 X7}
	true.

- : MULN-right-distributes-over-IADDN X3+X2=X1 MUL(X3,X4)=X7 _ _ MUL(X1,X4)=X5 MUL(X2,X4)=X6 
                                   X7+X6=X5
    <- MULN-total MUL(X1,X4)=X5
    <- MULN-right-distributes-over-ADDN X3+X2=X1 MUL(X1,X4)=X5 _ _
                                      MUL(X3,X4)=Y7 MUL(X2,X4)=X6 Y7+X6=X5
    <- MULN-deterministic MUL(X3,X4)=Y7 MUL(X3,X4)=X7 EQ/ EQ/ Y7=X7
    <- ADDN-respects-EQ Y7+X6=X5 Y7=X7 EQ/ EQ/ X7+X6=X5.

%worlds () (MULN-right-distributes-over-IADDN X1-X2=X3 MUL(X3,X4)=X7 
                                    %{=>}% X5 X6 MUL(X1,X4)=X5 MUL(X2,X4)=X6 X5-X6=X7).
%total {} (MULN-right-distributes-over-IADDN _ _ _ _ _ _ _).

%{%
#undef ADD
#define ADD(X,Y) X-Y
#undef ADDN
#define ADDN IADDN
#undef ADD_TOTAL
#ifdef IADD_TOTAL
#undef ADD_TOTAL 1
#endif
BEGIN_ELF
#include "distrib.i"
END_ELF
#undef ADD
#undef ADDN
#undef ADD_TOTAL
%}%
