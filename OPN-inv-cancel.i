%theorem IOPN-left-cancels : 
	forall* {X1} {X2} {X3} {X4} {X5} {X6}
	forall {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X4 X5 X6}
               {E1:EQ X1 X4} {E3:EQ X3 X6}
	exists {E2:EQ X2 X5}
	true.

- : IOPN-left-cancels OP(X3,X2)=X1 OP(X6,X5)=X4 X1=X4 X3=X6 X2=X5
   <- OPN-left-cancels OP(X3,X2)=X1 OP(X6,X5)=X4 X3=X6 X1=X4 X2=X5.

%worlds () (IOPN-left-cancels IOP(X1,X2)=X3 IOP(X4,X5)=X6 X1=X4 X3=X6 X2=X5).
%total {} (IOPN-left-cancels _ _ _ _ _).


%theorem IOPN-right-cancels : 
	forall* {X1} {X2} {X3} {X4} {X5} {X6}
	forall {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X4 X5 X6}
               {E2:EQ X2 X5} {E3:EQ X3 X6}
	exists {E1:EQ X1 X4}
	true.

- : IOPN-right-cancels OP(X3,X2)=X1 OP(X6,X5)=X4 X2=X5 X3=X6 X1=X4
    <- OPN-deterministic  OP(X3,X2)=X1 OP(X6,X5)=X4 X3=X6 X2=X5 X1=X4.

%worlds () (IOPN-right-cancels IOP(X1,X2)=X3 IOP(X4,X5)=X6 X2=X5 X3=X6 X1=X4).
%total {} (IOPN-right-cancels _ _ _ _ _).

%{%
#define CMPN GT
#define CMP(X,Y) X>Y
BEGIN_ELF
#include "OPN-inv-preserves-CMPN.i"
END_ELF
#undef CMP
#undef CMPN
%}%
