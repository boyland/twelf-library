


%%%% Definitions



GE : TYPE -> TYPE -> type.


GE/= : GE X Y
    <- EQ X Y.

GE/> : GE X Y
    <- GT X Y.



GE? : TYPE -> TYPE -> bool -> type.


GE?/yes : GE? X Y true
    <- GE X Y.

GE?/no : GE? X Y false
    <- GT Y X.



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



%%% Theorems about GE?


%theorem GE?-total*:
	forall	{N1} {N2}
	exists	{B}
		{G: GE? N1 N2 B}
	true.

%abbrev GE?-total = GE?-total* _ _ _.

%theorem GE?-total/L :
	forall*	{N1} {N2} {C}
	forall	{C: COMP N1 N2 C}
	exists	{B}
		{G: GE? N1 N2 B}
	true.

- : GE?-total/L (COMP/=) _ (GE?/yes (GE/= EQ/)).

- : GE?-total/L (COMP/> N1>N2) _ (GE?/yes (GE/> N1>N2)).

- : GE?-total/L (COMP/< N1<N2) _ (GE?/no N1<N2).

%worlds () (GE?-total/L _ _ _).
%total { } (GE?-total/L _ _ _).

- : GE?-total G
    <- COMP-total CMP
    <- GE?-total/L CMP _ G.

%worlds () (GE?-total* _ _ _ _).
%total { } (GE?-total* _ _ _ _).


%theorem GE?-unique:
	forall*	{N11} {N12} {B1}
		{N21} {N22} {B2}
	forall	{G1: GE? N11 N12 B1}
		{G2: GE? N21 N22 B2}
		{E1: EQ N11 N21}
		{E2: EQ N12 N22}
	exists	{BE: bool`eq B1 B2}
	true.

- : GE?-unique _ _ EQ/ EQ/ bool`eq/.

- : GE?-unique
	(GE?/yes N1>=N2) 
	(GE?/no N2>N1) EQ/ EQ/ BEQ
    <- GE-transitive-GT N1>=N2 N2>N1 N1>N1
    <- GT-anti-reflexive N1>N1 F
    <- bool`false-implies-eq F BEQ.

- : GE?-unique
	(GE?/no N2>N1)
	(GE?/yes N1>=N2)  EQ/ EQ/ BEQ 
    <- GE-transitive-GT N1>=N2 N2>N1 N1>N1
    <- GT-anti-reflexive N1>N1 F
    <- bool`false-implies-eq F BEQ.

%worlds () (GE?-unique _ _ _ _ _).
%total { } (GE?-unique _ _ _ _ _).

