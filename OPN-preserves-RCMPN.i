%theorem OPN-left-preserves-RCMPN* :
	forall* {X1} {X2} {X3} {X4} {X5}
        forall {R1:RCMPN X2 X4}
               {OP1:OPN X1 X2 X3} {OP2:OPN X1 X4 X5}
        exists {R2:RCMPN X3 X5}
	true.

- : OPN-left-preserves-RCMPN* CMP(X4,X2) OP(X1,X2)=X3 OP(X1,X4)=X5 CMP(X5,X3)
    <- OPN-left-preserves-CMPN* CMP(X4,X2) OP(X1,X4)=X5 OP(X1,X2)=X3 CMP(X5,X3).

%worlds () (OPN-left-preserves-RCMPN* RCMP(X2,X4) OP(X1,X2)=X3 OP(X1,X4)=X5 %{=>}% RCMP(X3,X5)).
%total {} (OPN-left-preserves-RCMPN* _ _ _ _).

%{%
#ifdef OP_CANCELS
%}%

%theorem OPN-left-cancels-RCMPN :
	forall* {X1} {X2} {X3} {Y1} {Y2} {Y3}
	forall {OP1:OPN X1 X2 X3} {OP2:OPN Y1 Y2 Y3} {E1:EQ X1 Y1} {R3:RCMPN X3 Y3} 
	exists {R2:RCMPN X2 Y2}
	true.

- : OPN-left-cancels-RCMPN OP(X1,X2)=X3 OP(X1,Y2)=X3 EQ/ CMP(Y3,X3) CMP(Y2,X2)
    <-  OPN-left-cancels-CMPN OP(X1,Y2)=X3 OP(X1,X2)=X3 EQ/ CMP(Y3,X3) CMP(Y2,X2).

%worlds () (OPN-left-cancels-RCMPN OP(X1,X2)=X3 OP(Y1,Y2)=Y3 X1=Y1 RCMP(X3,Y3) %{=>}% RCMP(X2,Y2)).
%total {} (OPN-left-cancels-RCMPN _ _ _ _ _).

%{%
#endif

#undef CMP
#define CMP(X,Y) RCMP(X,Y)
#undef CMPN
#define CMPN RCMPN
#define CMP_TRANSITIVE 1
BEGIN_ELF
#include "OPN-preserves-CMPN.i"
END_ELF
#undef CMP_TRANSITIVE
#undef CMPN
#undef CMP
%}%
