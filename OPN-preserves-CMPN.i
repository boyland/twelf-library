%{%
/* preserves-greater
 * preserving a greater than relation when performing
 * an operation.
 * This file assumes the theorems are unconditional,
 * not needings > 0 tests.
 */
/*
 * Requirements:
 * %theorem OPN-left-preserves-CMPN* :
 *	forall* {X1} {X2} {X3} {X4} {X5}
 *      forall {G:CMPN X2 X4}
 *             {O1:OPN X1 X2 X3} {O2:OPN X1 X4 X5}
 *      exists {GP:CMPN X3 X5}
 *	true.
 * OPN-commutative OPN-total CMPN-transitive
 * OP(,) OPN CMPN CMP(,)
 */

#ifndef WORLDS
#define WORLDS /* nothing */
#endif
#ifdef OP_TOTAL
%}%

%theorem OPN-left-preserves-CMPN :
	forall* {X1} {X2} {X4}
      	forall {G:CMPN X2 X4}
	exists {X3} {X5}
               {O1:OPN X1 X2 X3} {O2:OPN X1 X4 X5}
      	       {G2:CMPN X3 X5}
	true.

- : OPN-left-preserves-CMPN CMP(X2,X4) X3 X5 OP(X1,X2)=A3 OP(X1,X4)=X5 CMP(X3,X5)
    <- OPN-total OP(X1,X2)=A3 
    <- OPN-total OP(X1,X4)=X5
    <- OPN-left-preserves-CMPN* CMP(X2,X4) OP(X1,X2)=A3 OP(X1,X4)=X5 CMP(X3,X5).

%worlds () (OPN-left-preserves-CMPN CMP(X2,X4) %{=>}% X3 X5 OP(X1,X2)=A3 OP(X1,X4)=X5 CMP(X3,X5)).
%total {} (OPN-left-preserves-CMPN _ _ _ _ _ _).

%{%
#endif

#ifdef OP_COMMUTATIVE
%}%

%theorem OPN-right-preserves-CMPN* :
	forall* {X1} {X2} {X3} {X4} {X5}
	forall {G1:CMPN X1 X2} {O1:OPN X1 X3 X4} {O2:OPN X2 X3 X5}
	exists {G2:CMPN X4 X5}
	true.

- : OPN-right-preserves-CMPN* CMP(X1,X2) OP(X1,X3)=X4 OP(X2,X3)=X5 CMP(X4,X5)
    <- OPN-commutative OP(X1,X3)=X4 OP(X3,X1)=X4
    <- OPN-commutative OP(X2,X3)=X5 OP(X3,X2)=X5
    <- OPN-left-preserves-CMPN* CMP(X1,X2) OP(X3,X1)=X4 OP(X3,X2)=X5 CMP(X4,X5).

%worlds () (OPN-right-preserves-CMPN* CMP(X1,X2) OP(X1,X3)=X4 OP(X2,X3)=X5 %{=>}% CMP(X4,X5)).
%total {} (OPN-right-preserves-CMPN* _ _ _ _).

%{%
#ifdef OP_TOTAL
%}%

%theorem OPN-right-preserves-CMPN :
	forall* {X1} {X2} {X3}
	forall {G1:CMPN X1 X2} 
	exists {X4} {X5} {O1:OPN X1 X3 X4} {O2:OPN X2 X3 X5} {G2:CMPN X4 X5}
	true.

- : OPN-right-preserves-CMPN CMP(X1,X2) X4 X5 OP(X1,X3)=X4 OP(X2,X3)=X5 CMP(X4,X5)
    <- OPN-total OP(X1,X3)=X4 
    <- OPN-total OP(X2,X3)=X5
    <- OPN-right-preserves-CMPN* CMP(X1,X2) OP(X1,X3)=X4 OP(X2,X3)=X5 CMP(X4,X5).
%worlds () (OPN-right-preserves-CMPN CMP(X1,X2) %{=>}% X4 X5 OP(X1,X3)=X4 OP(X2,X3)=X5 CMP(X4,X5)).
%total {} (OPN-right-preserves-CMPN _ _ _ _ _ _).

%{%
#endif

#ifdef CMP_TRANSITIVE
#ifdef OP_TOTAL
%}%

%theorem OPN-preserves-CMPN* :
	forall* {X1} {X2} {X3} {Y1} {Y2} {Y3}
	forall {G1:CMPN X1 Y1} {G2:CMPN X2 Y2}
               {MX:OPN X1 X2 X3} {MY:OPN Y1 Y2 Y3}
        exists {G3:CMPN X3 Y3}
	true.

- : OPN-preserves-CMPN* CMP(X1,Y1) CMP(X2,Y2) OP(X1,X2)=X3 OP(Y1,Y2)=Y3 CMP(X3,Y3)
    <- OPN-total OP(Y1,X2)=X
    <- OPN-right-preserves-CMPN* CMP(X1,Y1) OP(X1,X2)=X3 OP(Y1,X2)=X CMP(X3,X)
    <- OPN-left-preserves-CMPN* CMP(X2,Y2) OP(Y1,X2)=X OP(Y1,Y2)=Y3 CMP(X,Y3)
    <- CMPN-transitive CMP(X3,X) CMP(X,Y3) CMP(X3,Y3).

%worlds () (OPN-preserves-CMPN* CMP(X1,Y1) CMP(X2,Y2) OP(X1,X2)=X3 OP(Y1,Y2)=Y3 %{=>}% CMP(X3,Y3)).
%total {} (OPN-preserves-CMPN* _ _ _ _ _).


%theorem OPN-preserves-CMPN :
	forall* {X1} {X2} {Y1} {Y2}
	forall {G1:CMPN X1 Y1} {G2:CMPN X2 Y2}
	exists {X3} {Y3} {MX:OPN X1 X2 X3} {MY:OPN Y1 Y2 Y3} {G3:CMPN X3 Y3}
	true.

- : OPN-preserves-CMPN CMP(X1,Y1) CMP(X2,Y2) X3 Y3 OP(X1,X2)=X3 OP(Y1,Y2)=Y3 CMP(X3,Y3)
    <- OPN-total OP(X1,X2)=X3
    <- OPN-total OP(Y1,Y2)=Y3
    <- OPN-preserves-CMPN* CMP(X1,Y1) CMP(X2,Y2) OP(X1,X2)=X3 OP(Y1,Y2)=Y3 CMP(X3,Y3).

%worlds () (OPN-preserves-CMPN CMP(X1,Y1) CMP(X2,Y2) %{=>}% X3 Y3 OP(X1,X2)=X3 OP(Y1,Y2)=Y3 CMP(X3,Y3)).
%total {} (OPN-preserves-CMPN _ _ _ _ _ _ _).

%{%
#else
#ifdef CMP_IFF_OP
%}%

%theorem OPN-preserves-CMPN* :
	forall* {X1} {X2} {X3} {Y1} {Y2} {Y3}
	forall {G1:CMPN X1 Y1} {G2:CMPN X2 Y2}
               {MX:OPN X1 X2 X3} {MY:OPN Y1 Y2 Y3}
        exists {G3:CMPN X3 Y3}
	true.

- : OPN-preserves-CMPN* CMP(X1,Y1) CMP(X2,Y2) OP(X1,X2)=X3 OP(Y1,Y2)=Y3 CMP(X3,Y3)
    <- CMPN-implies-OPN CMP(X2,Y2) W2 OP(W2,X2)=Y2
    <- OPN-commutative OP(W2,X2)=Y2 OP(X2,W2)=Y2
    <- OPN-associative-converse OP(X2,W2)=Y2 OP(Y1,Y2)=Y3 X OP(Y1,X2)=X OP(X,W2)=Y3
    <- OPN-right-preserves-CMPN* CMP(X1,Y1) OP(X1,X2)=X3 OP(Y1,X2)=X CMP(X3,X)
    <- OPN-left-preserves-CMPN* CMP(X2,Y2) OP(Y1,X2)=X OP(Y1,Y2)=Y3 CMP(X,Y3)
    <- CMPN-transitive CMP(X3,X) CMP(X,Y3) CMP(X3,Y3).

%worlds () (OPN-preserves-CMPN* CMP(X1,Y1) CMP(X2,Y2) OP(X1,X2)=X3 OP(Y1,Y2)=Y3 %{=>}% CMP(X3,Y3)).
%total {} (OPN-preserves-CMPN* _ _ _ _ _).


%{%
#endif /* CMP_IFF_OP */
#endif /* !OP_TOTAL */
#endif /* OP_TRANSITIVE */

#ifdef OP_CANCELS
%}%

%theorem OPN-right-cancels-CMPN :
	forall* {X1} {X2} {X3} {Y1} {Y2} {Y3}
	forall {OP1:OPN X1 X2 X3} {OP2:OPN Y1 Y2 Y3} {E2:EQ X2 Y2} {G3:CMPN X3 Y3} 
	exists {G1:CMPN X1 Y1}
	true.

- : OPN-right-cancels-CMPN OP(X1,X2)=X3 OP(Y1,Y2)=Y3 X2=Y2 CMP(X3,Y3) CMP(X1,Y1)
    <- OPN-commutative OP(X1,X2)=X3 OP(X2,X1)=X3
    <- OPN-commutative OP(Y1,Y2)=Y3 OP(Y2,Y1)=Y3
    <- OPN-left-cancels-CMPN OP(X2,X1)=X3 OP(Y2,Y1)=Y3 X2=Y2 CMP(X3,Y3) CMP(X1,Y1).

%worlds () (OPN-right-cancels-CMPN OP(X1,X2)=X3 OP(Y1,Y2)=Y3 X2=Y2 CMP(X3,Y3) %{=>}% CMP(X1,Y1)).
%total {} (OPN-right-cancels-CMPN _ _ _ _ _).

%{%
#endif
#endif
%}%
