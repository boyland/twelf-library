%theorem MULN-right-factors-over-IADDN :
	forall* {X1} {X2} {X4} {X5} {X6} {X7}
        forall {M14:MULN X1 X4 X5} {M24:MULN X2 X4 X6} {S56:IADDN X5 X6 X7}
        exists {X3} {S12:IADDN X1 X2 X3} {M34:MULN X3 X4 X7}
	true.

- : MULN-right-factors-over-IADDN MUL(X1,X4)=X5 MUL(X2,X4)=X6 X7+X6=X5 X3 X3+X2=X1 MUL(X3,X4)=X7
    <- ADDN-implies-GT X7+X6=X5 _ X5>X6
    <- MULN-right-cancels-GT MUL(X1,X4)=X5 MUL(X2,X4)=X6 EQ/ X5>X6 X1>X2
    <- GT-implies-ADDN X1>X2 X3 X3+X2=X1
    <- MULN-total MUL(X3,X4)=X7P
    <- MULN-right-distributes-over-ADDN* X3+X2=X1 MUL(X1,X4)=X5 MUL(X3,X4)=X7P MUL(X2,X4)=X6
                                       X7P+X6=X5
    <- ADDN-right-cancels X7P+X6=X5 X7+X6=X5 EQ/ EQ/ X7P=X7
    <- MULN-respects-EQ MUL(X3,X4)=X7P EQ/ EQ/ X7P=X7 MUL(X3,X4)=X7.

%worlds () (MULN-right-factors-over-IADDN MUL(X1,X4)=X5 MUL(X2,X4)=X6 X5-X6=X7
                                %{=>}% X3 X1-X2=X3 MUL(X3,X4)=X7 ).
%total {} (MULN-right-factors-over-IADDN _ _ _ _ _ _).

%{%
#define MUL_RIGHT_FACTORS 1
%}%
