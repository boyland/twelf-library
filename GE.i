


%%%% Definitions



GE : TYPE -> TYPE -> type.


GE/= : GE X Y
    <- EQ X Y.

GE/> : GE X Y
    <- GT X Y.




%%%% Theorems



%%% Theorems about GE

%{%
#define RELN GE
#define REL(X,Y) X>=Y
BEGIN_ELF
#include "RELN.i"
END_ELF
#undef REL
#undef RELN
%}%

%theorem GE-reflexive :
	forall {X}
	exists {G:GE X X}
	true.

- : GE-reflexive _ (GE/= EQ/).

%worlds () (GE-reflexive X %{=>}% X>=X).
%total {} (GE-reflexive _ _).


%theorem GE-transitive:
	forall* {X1} {X2} {X3}
	forall {G1:GE X1 X2} {G2:GE X2 X3}
	exists {G3:GE X1 X3}
	true.

- : GE-transitive (GE/= EQ/) (GE/= EQ/) (GE/= EQ/).

- : GE-transitive (GE/= EQ/) (GE/> X>X3) (GE/> X>X3).

- : GE-transitive (GE/> X1>X) (GE/= EQ/) (GE/> X1>X).

- : GE-transitive (GE/> X1>X2) (GE/> X2>X3) (GE/> X1>X3)
    <- GT-transitive X1>X2 X2>X3 X1>X3.

%worlds () (GE-transitive X1>=X2 X2>=X3 %{=>}% X1>=X3).
%total {} (GE-transitive _ _ _).


%theorem GE-anti-symmetric :
	forall* {X1} {X2}
	forall {G1:GE X1 X2} {G2:GE X2 X1}
        exists {E:EQ X1 X2}
	true.

- : GE-anti-symmetric (GE/= EQ/) _ EQ/.

- : GE-anti-symmetric _ (GE/= EQ/) EQ/.

- : GE-anti-symmetric (GE/> X1>X2) (GE/> X2>X1) X1=X2
    <- GT-anti-symmetric X1>X2 X2>X1 F
    <- false-implies-EQ F X1=X2.

%worlds () (GE-anti-symmetric X1>=X2 X2>=X1 %{=>}% X1=X2).
%total {} (GE-anti-symmetric _ _ _).


%theorem GE-transitive-GT:
	forall* {X1} {X2} {X3}
	forall {G1:GE X1 X2} {G2:GT X2 X3}
	exists {G3:GT X1 X3}
	true.

- : GE-transitive-GT (GE/= EQ/) X>X3 X>X3.

- : GE-transitive-GT (GE/> X1>X2) X2>X3 X1>X3
    <- GT-transitive X1>X2 X2>X3 X1>X3.

%worlds () (GE-transitive-GT X1>=X2 X2>X3 %{=>}% X1>X3).
%total {} (GE-transitive-GT _ _ _).


%theorem GT-transitive-GE:
	forall* {X1} {X2} {X3}
	forall {G1:GT X1 X2} {G2:GE X2 X3}
	exists {G3:GT X1 X3}
	true.

- : GT-transitive-GE X1>X2 (GE/= EQ/) X1>X2.

- : GT-transitive-GE X1>X2 (GE/> X2>X3) X1>X3
    <- GT-transitive X1>X2 X2>X3 X1>X3.

%worlds () (GT-transitive-GE X1>X2 X2>=X3 %{=>}% X1>X3).
%total {} (GT-transitive-GE _ _ _).
