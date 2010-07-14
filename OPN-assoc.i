%{%
#ifndef WORLDS
#define WORLDS /* nothing */
#endif
%}%
%theorem OPN-associative* :
	forall* {X1} {X2} {X12} {X3} {X23} {X123}
        forall {OP12:OPN X1 X2 X12} {OP12-3:OPN X12 X3 X123} {OP23:OPN X2 X3 X23}
        exists {OP1-23:OPN X1 X23 X123}
        true.

- : OPN-associative* OP(X1,X2)=X3 OP(X3,X4)=X7 OP(X2,X4)=X6 OP(X1,X6)=X7
    <- OPN-associative OP(X1,X2)=X3 OP(X3,X4)=X7 Y6 OP(X2,X4)=Y6 OP(X1,Y6)=X7
    <- OPN-deterministic OP(X2,X4)=Y6 OP(X2,X4)=X6 EQ/ EQ/ Y6=X6
    <- OPN-respects-EQ OP(X1,Y6)=X7 EQ/ Y6=X6 EQ/ OP(X1,X6)=X7.

%worlds () (OPN-associative* _ _ _ _).
%total {} (OPN-associative* _ _ _ _).


%theorem OPN-associative-converse :
	forall* {X1} {X2} {X4} {X6} {X7}
	forall {OP24:OPN X2 X4 X6} {OP16:OPN X1 X6 X7}
        exists {X3} {OP12:OPN X1 X2 X3} {OP34:OPN X3 X4 X7}
        true.

- : OPN-associative-converse OP(X2,X4)=X6 OP(X1,X6)=X7 _ OP(X1,X2)=X3 OP(X3,X4)=X7
    <- OPN-commutative OP(X2,X4)=X6 OP(X4,X2)=X6
    <- OPN-commutative OP(X1,X6)=X7 OP(X6,X1)=X7
    <- OPN-associative OP(X4,X2)=X6 OP(X6,X1)=X7 _ OP(X2,X1)=X3 OP(X4,X3)=X7
    <- OPN-commutative OP(X2,X1)=X3 OP(X1,X2)=X3
    <- OPN-commutative OP(X4,X3)=X7 OP(X3,X4)=X7.

%worlds () (OPN-associative-converse OP(X2,X4)=X6 OP(X1,X6)=X7 X3 OP(X1,X2)=X3 OP(X3,X4)=X7).
%total {} (OPN-associative-converse _ _ _ _ _).


%theorem OPN-associative-converse* :
	forall* {X1} {X2} {X3} {X4} {X6} {X7}
	forall {OP24:OPN X2 X4 X6} {OP16:OPN X1 X6 X7} {OP12:OPN X1 X2 X3} 
	exists {OP34:OPN X3 X4 X7}
        true.

- : OPN-associative-converse* OP(X2,X4)=X6 OP(X1,X6)=X7 OP(X1,X2)=X3 OP(X3,X4)=X7
    <- OPN-associative-converse OP(X2,X4)=X6 OP(X1,X6)=X7 X3P OP(X1,X2)=X3P OP(X3P,X4)=X7
    <- OPN-deterministic OP(X1,X2)=X3P OP(X1,X2)=X3 EQ/ EQ/ X3P=X3
    <- OPN-respects-EQ OP(X3P,X4)=X7 X3P=X3 EQ/ EQ/ OP(X3,X4)=X7.

%worlds () (OPN-associative-converse* OP(X2,X4)=X6 OP(X1,X6)=X7 OP(X1,X2)=X3 %{=>}% OP(X3,X4)=X7).
%total {} (OPN-associative-converse* _ _ _ _).

%{%
#ifndef INTRO_ASSOC_COMMUTATIVE
%}%
%% The following two theorems are useful for reordering elements
%% is a left-associative sequence of operations.
%{%
#define INTRO_ASSOC_COMMUTATIVE
#endif
%}%

%theorem OPN-assoc-commutative* :
	forall* {X1} {X2} {X3} {X4} {X5} {X7}
	forall {OP1:OPN X1 X2 X3} {OP2:OPN X3 X4 X7}
               {OP3:OPN X1 X4 X5} 
        exists {OP4:OPN X5 X2 X7}
	true.

- : OPN-assoc-commutative* OP(X1,X2)=X3 OP(X3,X4)=X7 OP(X1,X4)=X5 OP(X5,X2)=X7
    <- OPN-associative OP(X1,X2)=X3 OP(X3,X4)=X7 X6 OP(X2,X4)=X6 OP(X1,X6)=X7
    <- OPN-commutative OP(X2,X4)=X6 OP(X4,X2)=X6
    <- OPN-associative-converse* OP(X4,X2)=X6 OP(X1,X6)=X7 OP(X1,X4)=X5 OP(X5,X2)=X7.

%worlds () (OPN-assoc-commutative* OP(X1,X2)=X3 OP(X3,X4)=X7 OP(X1,X4)=X5 %{=>}% OP(X5,X2)=X7).
%total {} (OPN-assoc-commutative* _ _ _ _).


%theorem OPN-assoc-commutative :
	forall* {X1} {X2} {X3} {X4} {X7}
	forall {OP1:OPN X1 X2 X3} {OP2:OPN X3 X4 X7}
        exists {X5} {OP3:OPN X1 X4 X5} {OP4:OPN X5 X2 X7}
	true.

- : OPN-assoc-commutative OP(X1,X2)=X3 OP(X3,X4)=X7 X5 OP(X1,X4)=X5 OP(X5,X2)=X7
    <- OPN-associative OP(X1,X2)=X3 OP(X3,X4)=X7 X6 OP(X2,X4)=X6 OP(X1,X6)=X7
    <- OPN-commutative OP(X2,X4)=X6 OP(X4,X2)=X6
    <- OPN-associative-converse OP(X4,X2)=X6 OP(X1,X6)=X7 X5 OP(X1,X4)=X5 OP(X5,X2)=X7.

%worlds () (OPN-assoc-commutative OP(X1,X2)=X3 OP(X3,X4)=X7 %{=>}% X5 OP(X1,X4)=X5 OP(X5,X2)=X7).
%total {} (OPN-assoc-commutative _ _ _ _ _).

%{%
#ifndef INTRO_DOUBLE_ASSOCIATIVE
#define INTRO_DOUBLE_ASSOCIATIVE
%}%
%% The following theorem is a useful shortcut to
%% re-associate (AB)(CD) to (AC)(BD):
%{%
#endif
%}%

%theorem OPN-double-associative* :
	forall* {A} {B} {C} {D} {A+B} {C+D} {A+C} {B+D} {X}
	forall {AB:OPN A B A+B} {CD:OPN C D C+D} {ABCD:OPN A+B C+D X}
	       {AC:OPN A C A+C} {BD:OPN B D B+D} 
        exists {ACBD:OPN A+C B+D X}
	true.

- : OPN-double-associative* OP(X1,X2)=X3 OP(X4,X8)=XC OP(X3,XC)=XF OP(X1,X4)=X5 OP(X2,X8)=XA OP(X5,XA)=XF
    <- OPN-associative OP(X1,X2)=X3 OP(X3,XC)=XF XE OP(X2,XC)=XE OP(X1,XE)=XF
    <- OPN-commutative OP(X4,X8)=XC OP(X8,X4)=XC
    <- OPN-associative-converse* OP(X8,X4)=XC OP(X2,XC)=XE OP(X2,X8)=XA OP(XA,X4)=XE
    <- OPN-commutative OP(XA,X4)=XE OP(X4,XA)=XE
    <- OPN-associative-converse* OP(X4,XA)=XE OP(X1,XE)=XF OP(X1,X4)=X5 OP(X5,XA)=XF.

%worlds () (OPN-double-associative* OP(X1,X2)=X3 OP(X4,X8)=XC OP(X3,XC)=XF OP(X1,X4)=X5 OP(X2,X8)=XA
                            %{=>}% OP(X5,XA)=XF).
%total {} (OPN-double-associative* _ _ _ _ _ _).


%theorem OPN-double-associative :
	forall* {A} {B} {C} {D} {A+B} {C+D} {X}
	forall {AB:OPN A B A+B} {CD:OPN C D C+D} {ABCD:OPN A+B C+D X}
	exists {A+C} {B+D} {AC:OPN A C A+C} {BD:OPN B D B+D} 
               {ACBD:OPN A+C B+D X}
	true.

- : OPN-double-associative OP(X1,X2)=X3 OP(X4,X8)=XC OP(X3,XC)=XF X5 XA OP(X1,X4)=X5 OP(X2,X8)=XA OP(X5,XA)=XF
    <- OPN-associative OP(X1,X2)=X3 OP(X3,XC)=XF XE OP(X2,XC)=XE OP(X1,XE)=XF
    <- OPN-commutative OP(X4,X8)=XC OP(X8,X4)=XC
    <- OPN-associative-converse OP(X8,X4)=XC OP(X2,XC)=XE XA OP(X2,X8)=XA OP(XA,X4)=XE
    <- OPN-commutative OP(XA,X4)=XE OP(X4,XA)=XE
    <- OPN-associative-converse OP(X4,XA)=XE OP(X1,XE)=XF X5 OP(X1,X4)=X5 OP(X5,XA)=XF.

%worlds () (OPN-double-associative _ _ _ _ _ _ _ _).
%total { } (OPN-double-associative _ _ _ _ _ _ _ _).
