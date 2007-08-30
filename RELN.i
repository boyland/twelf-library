%theorem false-implies-RELN :
	forall* {X1} {X2}
	forall {F:void}
	exists {G:RELN X1 X2}
	true.

%worlds () (false-implies-RELN _ _).
%total { } (false-implies-RELN _ _).


%theorem RELN-respects-EQ :
	forall* {X1} {X2} {Y1} {Y2}
	forall {D1:RELN X1 X2} {E1:EQ X1 Y1} {E2:EQ X2 Y2}
	exists {D2:RELN Y1 Y2}
	true.

- : RELN-respects-EQ REL(X1,X2) EQ/ EQ/ REL(X1,X2).

%worlds () (RELN-respects-EQ _ _ _ _).
%total { } (RELN-respects-EQ _ _ _ _).
