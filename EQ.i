%theorem false-implies-EQ :
	forall* {X1} {X2}
	forall {F:void}
	exists {E:EQ X1 X2}
	true.

%worlds () (false-implies-EQ _ _).
%total { } (false-implies-EQ _ _).


%theorem meta-EQ :
	forall {X1} {X2} {E:EQ X1 X2}
	true.

- : meta-EQ _ _ EQ/.

%worlds () (meta-EQ _ _ _).
%total { } (meta-EQ _ _ _).
%reduces X = Y (meta-EQ X Y _).

	
%theorem EQ-reflexive : 
	forall {X} 
	exists {E:EQ X X} 
	true.

- : EQ-reflexive _ EQ/.

%worlds () (EQ-reflexive _ _).
%total { } (EQ-reflexive _ _).


%theorem EQ-symmetric : 
	forall* {X} {Y}
	forall {E:EQ X Y}
	exists {F:EQ Y X}
	true.

- : EQ-symmetric (EQ/) (EQ/).

%worlds () (EQ-symmetric _ _).
%total { } (EQ-symmetric _ _).


%theorem EQ-transitive : 
	forall* {X} {Y} {Z}
	forall {E1:EQ X Y} {E2:EQ Y Z}
	exists {F:EQ X Z}
	true.

- : EQ-transitive (EQ/) (EQ/) (EQ/).

%worlds () (EQ-transitive _ _ _).
%total { } (EQ-transitive _ _ _).

