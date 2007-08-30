%{%
#define CMPN NE
#define CMP(X,Y) X<>Y
%}%

%theorem OPN-left-preserves-NE* :
	forall* {X1} {X2} {X3} {X4} {X5}
        forall {G:NE X2 X4}
               {OP1:OPN X1 X2 X3} {OP2:OPN X1 X4 X5}
        exists {G2:NE X3 X5}
	true.

- : OPN-left-preserves-NE* (NE/< X4>X2) OP(X1,X2)=X3 OP(X1,X4)=X5 (NE/< X5>X3)
    <- OPN-left-preserves-GT* X4>X2 OP(X1,X4)=X5 OP(X1,X2)=X3 X5>X3.

- : OPN-left-preserves-NE* (NE/> X2>X4) OP(X1,X2)=X3 OP(X1,X4)=X5 (NE/> X3>X5)
    <- OPN-left-preserves-GT* X2>X4 OP(X1,X2)=X3 OP(X1,X4)=X5 X3>X5.

%worlds () (OPN-left-preserves-NE* X2<>X4 OP(X1,X2)=X3 OP(X1,X4)=X5 %{=>}% X3<>X5).
%total {} (OPN-left-preserves-NE* _ _ _ _).


%theorem OPN-left-cancels-NE :
	forall* {X1} {X2} {X3} {Y1} {Y2} {Y3}
	forall {OP1:OPN X1 X2 X3} {OP2:OPN Y1 Y2 Y3} {E1:EQ X1 Y1} {G3:NE X3 Y3} 
	exists {G2:NE X2 Y2}
	true.

- : OPN-left-cancels-NE OP(X1,X2)=X3 OP(X1,Y2)=Y3 EQ/ (NE/< Y3>X3) (NE/< Y2>X2)
    <- OPN-left-cancels-GT OP(X1,Y2)=Y3 OP(X1,X2)=X3 EQ/ Y3>X3 Y2>X2.

- : OPN-left-cancels-NE OP(X1,X2)=X3 OP(X1,Y2)=Y3 EQ/ (NE/> X3>Y3) (NE/> X2>Y2)
    <- OPN-left-cancels-GT OP(X1,X2)=X3 OP(X1,Y2)=Y3 EQ/ X3>Y3 X2>Y2.

%worlds () (OPN-left-cancels-NE OP(X1,X2)=X3 OP(Y1,Y2)=Y3 X1=Y1 X3<>Y3 %{=>}% X2<>Y2).
%total {} (OPN-left-cancels-NE _ _ _ _ _).

%{%
BEGIN_ELF
#include "OPN-preserves-CMPN.i"
END_ELF
#undef CMPN
#undef CMP
%}%
