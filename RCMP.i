



%%%% Definitions


%abbrev RCMPN = [X] [Y] CMPN Y X.




%%%% Theorems about RCMPN

%{%
#define RELN RCMPN
#define REL(X,Y) RCMP(X,Y)
BEGIN_ELF
#include "RELN.i"
END_ELF
#undef REL
#undef RELN

#ifdef INC_EQ
#define RESULT {E3:EQ X1 X2}
#else
#define RESULT {F:void}
#endif

/** It would be nice to write abbreviations such as
 * %abbrev RCMPN-anti-symmetric = [A] [B] CMPN-anti-symmetric B A.
 * But these fall afoul of Twelf's type checker.
 */
%}%

%theorem RCMPN-anti-symmetric :
	forall* {X1} {X2}
	forall {G1:RCMPN X1 X2} {G2:RCMPN X2 X1}
	exists RESULT
	true.

- : RCMPN-anti-symmetric CMP(X2,X1) CMP(X1,X2) R
    <- CMPN-anti-symmetric CMP(X1,X2) CMP(X2,X1) R.

%worlds () (RCMPN-anti-symmetric _ _ _).
%total {} (RCMPN-anti-symmetric _ _ _).

%{%
#undef RESULT
%}%

%theorem RCMPN-transitive : 
	forall* {X1} {X2} {X3}
	forall {G1:RCMPN X1 X2} {G2:RCMPN X2 X3}
	exists {G3:RCMPN X1 X3}
	true.

- : RCMPN-transitive RCMP(X1,X2) RCMP(X2,X3) RCMP(X1,X3)
    <- CMPN-transitive RCMP(X2,X3) RCMP(X1,X2) RCMP(X1,X3).

%worlds () (RCMPN-transitive RCMP(X1,X2) RCMP(X2,X3) RCMP(X1,X3)).
%total {} (RCMPN-transitive _ _ _).


