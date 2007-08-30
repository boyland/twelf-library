


%%%% Definitions



NE : TYPE -> TYPE -> type.


NE/< : NE X Y
    <- GT Y X.

NE/> : NE X Y
    <- GT X Y.




EQ? : TYPE -> TYPE -> bool -> type.


EQ?/yes : EQ? X X true.

EQ?/no : EQ? X Y false
    <- NE X Y.




%%%% Theorems



%%% Theorems about NE

%{%
#define RELN NE
#define REL(X,Y) X<>Y
BEGIN_ELF
#include "RELN.i"
END_ELF
#undef REL
#undef RELN
%}%

%theorem NE-anti-reflexive :
	forall* {X}
	forall {R:NE X X}
	exists {F:void}
	true.

- : NE-anti-reflexive (NE/< X<X) F
    <- GT-anti-reflexive X<X F.

- : NE-anti-reflexive (NE/> X>X) F
    <- GT-anti-reflexive X>X F.

%worlds () (NE-anti-reflexive X<>X %{=>}% _).
%total {} (NE-anti-reflexive _ _).


%theorem NE-symmetric :
	forall* {X} {Y}
	forall {R1:NE X Y}
	exists {R2:NE Y X}
	true.

- : NE-symmetric (NE/< X<Y) (NE/> X<Y).

- : NE-symmetric (NE/> X>Y) (NE/< X>Y).

%worlds () (NE-symmetric X<>Y %{=>}% Y<>X).
%total {} (NE-symmetric _ _).


%theorem EQ-NE-implies-false :
	forall* {X} {Y}
	forall {D1:EQ X Y} {D2:NE X Y}
	exists {F:void}
	true.

- : EQ-NE-implies-false EQ/ X<>X F
    <- NE-anti-reflexive X<>X F.

%worlds () (EQ-NE-implies-false X=Y X<>Y %{=>}% _).
%total {} (EQ-NE-implies-false _ _ _).


%theorem GE-NE-implies-GT :
	forall* {X} {Y}
	forall {D1:GE X Y} {D2:NE X Y}
	exists {D3:GT X Y}
	true.

- : GE-NE-implies-GT (GE/> X>Y) _ X>Y.

- : GE-NE-implies-GT (GE/= EQ/) X<>X X>X
    <- NE-anti-reflexive X<>X F
    <- false-implies-GT F X>X.

%worlds () (GE-NE-implies-GT X>=Y X<>Y %{=>}% X>Y).
%total {} (GE-NE-implies-GT _ _ _).


%theorem EQ?-total* :
	forall {M} {N}
	exists {B} {T:EQ? M N B}
	true.

%theorem EQ?-total*/L :
	forall* {M} {N} {C}
	forall {CMP:COMP M N C}
	exists {B} {T:EQ? M N B}
	true.

- : EQ?-total*/L COMP/= true EQ?/yes.

- : EQ?-total*/L (COMP/< X<Y) false (EQ?/no (NE/< X<Y)).

- : EQ?-total*/L (COMP/> X>Y) false (EQ?/no (NE/> X>Y)).

%worlds () (EQ?-total*/L _ _ _).
%total { } (EQ?-total*/L _ _ _).

- : EQ?-total* M N B T
    <- COMP-total CMP
    <- EQ?-total*/L CMP B T.

%worlds () (EQ?-total* _ _ _ _).
%total { } (EQ?-total* _ _ _ _).


%abbrev EQ?-total = EQ?-total* _ _ _.
