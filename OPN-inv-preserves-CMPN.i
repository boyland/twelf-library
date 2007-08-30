%{%
#ifdef CMP_SYMMETRIC
#define INVERTS preserves
#define CANCELS_INVERTS cancels
#define SWAP(X,Y) X Y
#define SWCMP(X,Y) CMP(X,Y)
#define ECMP(X,Y) CMP(X,Y)
/* and add    <- CMPN-symmetric CMP(X,Y) CMP(Y,X). */
#else
#define INVERTS inverts
#define CANCELS_INVERTS cancels-inverts
#define SWAP(X,Y) Y X
#define SWCMP(X,Y) CMP(Y,X)
#define ECMP(X,Y) CMP(X,Y).
#endif
%}%

%theorem IOPN-left-INVERTS-CMPN* :
	forall* {X1} {X2} {X3} {X4} {X5}
        forall {G:CMPN X2 X4}
               {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X1 X4 X5}
        exists {GP:CMPN SWAP(X3,X5)}
	true.

- : IOPN-left-INVERTS-CMPN* CMP(X2,X4) OP(X3,X2)=X1 OP(X5,X4)=X1 SWCMP(X3,X5)
    <- OPN-total OP(X3,X4)=X7
    <- OPN-left-preserves-CMPN* CMP(X2,X4) OP(X3,X2)=X1 OP(X3,X4)=X7 CMP(X1,X7)
    <- OPN-right-cancels-CMPN OP(X5,X4)=X1 OP(X3,X4)=X7 EQ/ CMP(X1,X7) ECMP(X5,X3)
%{%
#ifdef CMP_SYMMETRIC
%}%
    <- CMPN-symmetric CMP(X5,X3) CMP(X3,X5).
%{%
#endif
%}%

%worlds () (IOPN-left-INVERTS-CMPN* CMP(X2,X4) IOP(X1,X2)=X3 IOP(X1,X4)=X5 %{=>}% SWCMP(X3,X5)).
%total {} (IOPN-left-INVERTS-CMPN* _ _ _ _).

%{%
#ifdef IOP_TOTAL
%}%

%theorem IOPN-left-INVERTS-CMPN :
	forall* {X1} {X2} {X4}
        forall {G:CMPN X2 X4}
        exists {X3} {X5} {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X1 X4 X5}
               {GP:CMPN SWAP(X3,X5)}
	true.

- : IOPN-left-INVERTS-CMPN CMP(X2,X4) X3 X5 IOP(X1,X2)=X3 IOP(X1,X4)=X5 SWCMP(X3,X5)
    <- IOPN-total IOP(X1,X2)=X3
    <- IOPN-total IOP(X1,X4)=X5
    <- IOPN-left-INVERTS-CMPN* CMP(X2,X4) IOP(X1,X2)=X3 IOP(X1,X4)=X5 SWCMP(X3,X5).

%worlds () (IOPN-left-INVERTS-CMPN CMP(X2,X4) %{=>}% X3 X5 IOP(X1,X2)=X3 IOP(X1,X4)=X5 SWCMP(X3,X5)).
%total {} (IOPN-left-INVERTS-CMPN _ _ _ _ _ _).

%{%
#endif
%}%

%theorem IOPN-right-preserves-CMPN* :
	forall* {X1} {X2} {X3} {X4} {X5}
        forall {G:CMPN X1 X2}
               {IOP1:IOPN X1 X3 X4} {IOP2:IOPN X2 X3 X5}
        exists {GP:CMPN X4 X5}
	true.

- : IOPN-right-preserves-CMPN*  CMP(X1,X2) OP(X4,X3)=X1 OP(X5,X3)=X2 CMP(X4,X5)
    <- OPN-right-cancels-CMPN OP(X4,X3)=X1 OP(X5,X3)=X2 EQ/ CMP(X1,X2) CMP(X4,X5).

%worlds () (IOPN-right-preserves-CMPN* CMP(X1,X2) IOP(X1,X3)=X4 IOP(X2,X3)=X5 %{=>}% CMP(X4,X5)).
%total {} (IOPN-right-preserves-CMPN* _ _ _ _).

%{%
#ifdef IOP_TOTAL
%}%

%theorem IOPN-right-preserves-CMPN :
	forall* {X1} {X2} {X3}
        forall {G:CMPN X1 X2}
        exists {X4} {X5} {IOP1:IOPN X1 X3 X4} {IOP2:IOPN X2 X3 X5}
               {GP:CMPN X4 X5}
	true.

- : IOPN-right-preserves-CMPN CMP(X1,X2) X4 X5 IOP(X1,X3)=X4 IOP(X2,X3)=X5 CMP(X4,X5)
    <- IOPN-total IOP(X1,X3)=X4
    <- IOPN-total IOP(X2,X3)=X5
    <- IOPN-right-preserves-CMPN* CMP(X1,X2) IOP(X1,X3)=X4 IOP(X2,X3)=X5 CMP(X4,X5).

%worlds () (IOPN-right-preserves-CMPN CMP(X1,X2) %{=>}% X4 X5 IOP(X1,X3)=X4 IOP(X2,X3)=X5 CMP(X4,X5)).
%total {} (IOPN-right-preserves-CMPN _ _ _ _ _ _).

%{%
#endif
%}%

%theorem IOPN-left-CANCELS_INVERTS-CMPN :
	forall* {X1} {X2} {X3} {X4} {X5} {X6}
	forall {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X4 X5 X6}
               {E:EQ X1 X4} {G:CMPN X3 X6}
        exists {GP:CMPN SWAP(X2,X5)}
	true.

- : IOPN-left-CANCELS_INVERTS-CMPN OP(X3,X2)=X1 OP(X6,X5)=X4 X1=X4 CMP(X3,X6) SWCMP(X2,X5)
    <- OPN-total OP(X6,X2)=X7
    <- OPN-right-preserves-CMPN* CMP(X3,X6) OP(X3,X2)=X1 OP(X6,X2)=X7 CMP(X1,X7)
    <- EQ-symmetric X1=X4 X4=X1
    <- OPN-respects-EQ OP(X6,X5)=X4 EQ/ EQ/ X4=X1 OP(X6,X5)=X1
    <- OPN-left-cancels-CMPN OP(X6,X5)=X1 OP(X6,X2)=X7 EQ/ CMP(X1,X7) ECMP(X5,X2)
%{%
#ifdef CMP_SYMMETRIC
%}%
    <- CMPN-symmetric CMP(X5,X2) CMP(X2,X5).
%{%
#endif
%}%

%worlds () (IOPN-left-CANCELS_INVERTS-CMPN IOP(X1,X2)=X3 IOP(X4,X5)=X6 X1=X4 CMP(X3,X6) 
                                  %{=>}% SWCMP(X2,X5)).
%total {} (IOPN-left-CANCELS_INVERTS-CMPN _ _ _ _ _).


%theorem IOPN-right-cancels-CMPN :
	forall* {X1} {X2} {X3} {X4} {X5} {X6}
	forall {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X4 X5 X6}
               {E2:EQ X2 X5} {G3:CMPN X3 X6}
        exists {G1:CMPN X1 X4}
	true.

- : IOPN-right-cancels-CMPN OP(X3,X2)=X1 OP(X6,X5)=X4 X2=X5 CMP(X3,X6) CMP(X1,X4)
    <- OPN-respects-EQ OP(X3,X2)=X1 EQ/ X2=X5 EQ/ OP(X3,X5)=X1
    <- OPN-right-preserves-CMPN* CMP(X3,X6) OP(X3,X5)=X1 OP(X6,X5)=X4 CMP(X1,X4).

%worlds () (IOPN-right-cancels-CMPN IOP(X1,X2)=X3 IOP(X4,X5)=X6 X2=X5 CMP(X3,X6) 
                           %{=>}% CMP(X1,X4)).
%total {} (IOPN-right-cancels-CMPN _ _ _ _ _).

%{%
#undef INVERTS
#undef CANCELS_INVERTS
#undef SWAP
#undef SWCMP
#undef ECMP
%}%
