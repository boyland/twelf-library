#define CMP(X,Y) X>=Y
#define CMPN GE
#define RCMP(X,Y) X<=Y
#define RCMPN LE
#define INC_EQ 1
#include "RCMP.i"
#undef INC_EQ
#undef RCMPN
#undef RCMP
#undef CMPN
#undef CMP

%abbrev LE-reflexive = GE-reflexive.

%theorem LE-transitive-LT:
	forall* {X1} {X2} {X3}
	forall {L1:LE X1 X2} {L2:LT X2 X3}
	exists {L3:LT X1 X3}
	true.
- : LE-transitive-LT X2>=X1 X3>X2 X3>X1
    <- GT-transitive-GE X3>X2 X2>=X1 X3>X1.
%worlds () (LE-transitive-LT X1<=X2 X2<X3 %{=>}% X1<X3).
%total {} (LE-transitive-LT _ _ _).

%theorem LT-transitive-LE:
	forall* {X1} {X2} {X3}
	forall {L1:LT X1 X2} {L2:LE X2 X3}
	exists {L3:LT X1 X3}
	true.
- : LT-transitive-LE X2>X1 X3>=X2 X3>X1
    <- GE-transitive-GT X3>=X2 X2>X1 X3>X1.
%worlds () (LT-transitive-LE X1<X2 X2<=X3 %{=>}% X1<X3).
%total {} (LT-transitive-LE _ _ _).
