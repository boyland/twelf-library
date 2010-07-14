


%%%% Definitions

%abbrev IOPN = [X1] [X2] [X3] OPN X3 X2 X1.




%%%% Theorems


%%% Theorems about IOPN


%abbrev false-implies-IOPN = false-implies-OPN.


%theorem IOPN-respects-EQ :
	forall* {X1} {X2} {X3} {X4} {X5} {X6}
	forall {D:IOPN X1 X2 X3} {E1:EQ X1 X4} {E2:EQ X2 X5} {E3:EQ X3 X6}
        exists {DP:IOPN X4 X5 X6}
        true.

- : IOPN-respects-EQ S EQ/ EQ/ EQ/ S.

%worlds () (IOPN-respects-EQ _ _ _ _ _).
%total {} (IOPN-respects-EQ _ _ _ _ _).

%{%
#ifdef OP_CANCELS
%}%

%theorem IOPN-deterministic :
	forall* {X1} {X2} {X3} {X4} {X5} {X6}
	forall {S:IOPN X1 X2 X3} {SP:IOPN X4 X5 X6}
               {E1:EQ X1 X4} {E2:EQ X2 X5}
	exists {E3:EQ X3 X6}
	true.

%abbrev IOPN-unique = IOPN-deterministic.

- : IOPN-deterministic OP(X3,X2)=X1 OP(X6,X5)=X4 X1=X4 X2=X5 X3=X6
    <- OPN-right-cancels OP(X3,X2)=X1 OP(X6,X5)=X4 X2=X5 X1=X4 X3=X6.

%worlds () (IOPN-deterministic IOP(X1,X2)=X3 IOP(X4,X5)=X6 X1=X4 X2=X5 X3=X6).
%total {} (IOPN-deterministic _ _ _ _ _).

%{%
#endif
%}%
