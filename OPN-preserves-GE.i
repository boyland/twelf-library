%{%
#define CMPN GE
#define CMP(X,Y) X>=Y
#define CMP_TRANSITIVE 1
%}%

%theorem OPN-left-preserves-GE* :
	forall* {X1} {X2} {X3} {X4} {X5}
        forall {G:GE X2 X4}
               {OP1:OPN X1 X2 X3} {OP2:OPN X1 X4 X5}
        exists {G2:GE X3 X5}
	true.

- : OPN-left-preserves-GE* (GE/= EQ/) OP(X1,X2)=X3 OP(X1,X2)=X5 (GE/= X3=X5)
    <- OPN-deterministic OP(X1,X2)=X3 OP(X1,X2)=X5 EQ/ EQ/ X3=X5.

- : OPN-left-preserves-GE* (GE/> X2>X4) OP(X1,X2)=X3 OP(X1,X4)=X5 (GE/> X3>X5)
    <- OPN-left-preserves-GT* X2>X4 OP(X1,X2)=X3 OP(X1,X4)=X5 X3>X5.

%worlds () (OPN-left-preserves-GE* X2>=X4 OP(X1,X2)=X3 OP(X1,X4)=X5 %{=>}% X3>=X5).
%total {} (OPN-left-preserves-GE* _ _ _ _).


%theorem OPN-left-cancels-GE :
	forall* {X1} {X2} {X3} {Y1} {Y2} {Y3}
	forall {OP1:OPN X1 X2 X3} {OP2:OPN Y1 Y2 Y3} {E1:EQ X1 Y1} {G3:GE X3 Y3} 
	exists {G2:GE X2 Y2}
	true.

- : OPN-left-cancels-GE OP(X1,X2)=X3 OP(X1,Y2)=X3 EQ/ (GE/= EQ/) (GE/= X2=Y2)
    <- OPN-left-cancels OP(X1,X2)=X3 OP(X1,Y2)=X3 EQ/ EQ/ X2=Y2.

- : OPN-left-cancels-GE OP(X1,X2)=X3 OP(X1,Y2)=Y3 EQ/ (GE/> X3>Y3) (GE/> X2>Y2)
    <- OPN-left-cancels-GT OP(X1,X2)=X3 OP(X1,Y2)=Y3 EQ/ X3>Y3 X2>Y2.

%worlds () (OPN-left-cancels-GE OP(X1,X2)=X3 OP(Y1,Y2)=Y3 X1=Y1 X3>=Y3 %{=>}% X2>=Y2).
%total {} (OPN-left-cancels-GE _ _ _ _ _).

%{%
BEGIN_ELF
#include "OPN-preserves-CMPN.i"
END_ELF
#undef CMP_TRANSITIVE
#undef CMPN
#undef CMP
%}%
