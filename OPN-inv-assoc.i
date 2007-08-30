%theorem OPN-associates-with-IOPN* :
	forall* {X1} {X2} {X3} {X4} {X6} {X7}
	forall {OP1:OPN X1 X2 X3} {IOP1:IOPN X3 X4 X7} {IOP2:IOPN X2 X4 X6} 
	exists {OP2:OPN X1 X6 X7}
        true.

- : OPN-associates-with-IOPN* OP(X1,X2)=X3 OP(X7,X4)=X3 OP(X6,X4)=X2 OP(X1,X6)=X7
    <- OPN-associative-converse OP(X6,X4)=X2 OP(X1,X2)=X3 X7P OP(X1,X6)=X7P X7P+X4=X3
    <- OPN-right-cancels X7P+X4=X3 OP(X7,X4)=X3 EQ/ EQ/ X7P=X7
    <- OPN-respects-EQ OP(X1,X6)=X7P EQ/ EQ/ X7P=X7 OP(X1,X6)=X7.

%worlds () (OPN-associates-with-IOPN* OP(X1,X2)=X3 IOP(X3,X4)=X7 IOP(X2,X4)=X6 
                              %{=>}% OP(X1,X6)=X7).
%total {} (OPN-associates-with-IOPN* _ _ _ _).

%{%
#ifdef IOP_TOTAL
%}%

%theorem OPN-associates-with-IOPN :
	forall* {X1} {X2} {X3} {X4} {X7}
	forall {OP1:OPN X1 X2 X3} {IOP1:IOPN X3 X4 X7}
        exists {X6} {IOP2:IOPN X2 X4 X6} {OP2:OPN X1 X6 X7}
        true.

- : OPN-associates-with-IOPN OP(X1,X2)=X3 IOP(X3,X4)=X7 X6 IOP(X2,X4)=X6 OP(X1,X6)=X7
    <- IOPN-total IOP(X2,X4)=X6
    <- OPN-associates-with-IOPN* OP(X1,X2)=X3 IOP(X3,X4)=X7 IOP(X2,X4)=X6 OP(X1,X6)=X7.

%worlds () (OPN-associates-with-IOPN OP(X1,X2)=X3 IOP(X3,X4)=X7 
                             %{=>}% X6 IOP(X2,X4)=X6 OP(X1,X6)=X7).
%total {} (OPN-associates-with-IOPN _ _ _ _ _).

%{%
#endif
%}%

%theorem OPN-associates-with-IOPN-converse* :
	forall* {X1} {X2} {X3} {X4} {X6} {X7}
        forall {IOP2:IOPN X2 X4 X6} {OP2:OPN X1 X6 X7} {OP1:OPN X1 X2 X3} 
	exists {IOP1:IOPN X3 X4 X7} 
        true.

- : OPN-associates-with-IOPN-converse* OP(X6,X4)=X2 OP(X1,X6)=X7 OP(X1,X2)=X3 OP(X7,X4)=X3
    <- OPN-associative-converse* OP(X6,X4)=X2 OP(X1,X2)=X3 OP(X1,X6)=X7 OP(X7,X4)=X3.

%worlds () (OPN-associates-with-IOPN-converse* IOP(X2,X4)=X6 OP(X1,X6)=X7 OP(X1,X2)=X3 
                                       %{=>}% IOP(X3,X4)=X7).
%total {} (OPN-associates-with-IOPN-converse* _ _ _ _).


%theorem OPN-associates-with-IOPN-converse :
	forall* {X1} {X2} {X4} {X6} {X7}
        forall {IOP2:IOPN X2 X4 X6} {OP2:OPN X1 X6 X7} 
        exists {X3} {OP1:OPN X1 X2 X3} {IOP1:IOPN X3 X4 X7} 
        true.

- : OPN-associates-with-IOPN-converse OP(X6,X4)=X2 OP(X1,X6)=X7 X3 OP(X1,X2)=X3 OP(X7,X4)=X3
    <- OPN-total OP(X1,X2)=X3
    <- OPN-associates-with-IOPN-converse* OP(X6,X4)=X2 OP(X1,X6)=X7 OP(X1,X2)=X3 OP(X7,X4)=X3.
%worlds () (OPN-associates-with-IOPN-converse IOP(X2,X4)=X6 OP(X1,X6)=X7 
                                      %{=>}% X3 OP(X1,X2)=X3 IOP(X3,X4)=X7).
%total {} (OPN-associates-with-IOPN-converse _ _ _ _ _).


%theorem IOPN-associates-from-OPN* :
	forall* {X1} {X2} {X3} {X4} {X6} {X7}
	forall {IOP1:IOPN X1 X2 X3} {OP1:OPN X3 X4 X7} {IOP2:IOPN X2 X4 X6}
        exists {IOP3:IOPN X1 X6 X7}
        true.

- : IOPN-associates-from-OPN* OP(X3,X2)=X1 OP(X3,X4)=X7 OP(X6,X4)=X2 OP(X7,X6)=X1
    <- OPN-commutative OP(X6,X4)=X2 OP(X4,X6)=X2
    <- OPN-associative-converse* OP(X4,X6)=X2 OP(X3,X2)=X1 OP(X3,X4)=X7 OP(X7,X6)=X1.

%worlds () (IOPN-associates-from-OPN* IOP(X1,X2)=X3 OP(X3,X4)=X7 IOP(X2,X4)=X6 %{=>}% IOP(X1,X6)=X7).
%total {} (IOPN-associates-from-OPN* _ _ _ _).

%{%
#ifdef IOP_TOTAL
%}%

%theorem IOPN-associates-from-OPN :
	forall* {X1} {X2} {X3} {X4} {X7}
	forall {IOP1:IOPN X1 X2 X3} {OP1:OPN X3 X4 X7}
        exists {X6} {IOP2:IOPN X2 X4 X6} {IOP3:IOPN X1 X6 X7}
        true.

- : IOPN-associates-from-OPN OP(X3,X2)=X1 OP(X3,X4)=X7 X6 OP(X6,X4)=X2 OP(X7,X6)=X1
    <- IOPN-total OP(X6,X4)=X2
    <- IOPN-associates-from-OPN* OP(X3,X2)=X1 OP(X3,X4)=X7 OP(X6,X4)=X2 OP(X7,X6)=X1.

%worlds () (IOPN-associates-from-OPN IOP(X1,X2)=X3 OP(X3,X4)=X7 %{=>}% X6 IOP(X2,X4)=X6 IOP(X1,X6)=X7).
%total {} (IOPN-associates-from-OPN _ _ _ _ _).

%{%
#endif
%}%

%theorem IOPN-associates-from-OPN-converse* :
	forall* {X1} {X2} {X3} {X4} {X6} {X7} 
	forall {IOP2:IOPN X2 X4 X6} {IOP3:IOPN X1 X6 X7} {IOP1:IOPN X1 X2 X3} 
        exists {OP1:OPN X3 X4 X7} 
        true.

- : IOPN-associates-from-OPN-converse* OP(X6,X4)=X2 OP(X7,X6)=X1 OP(X3,X2)=X1 OP(X3,X4)=X7
    <- OPN-commutative OP(X6,X4)=X2 OP(X4,X6)=X2
    <- OPN-associative-converse OP(X4,X6)=X2 OP(X3,X2)=X1 X7P OP(X3,X4)=X7P X7P+X6=X1
    <- OPN-right-cancels X7P+X6=X1 OP(X7,X6)=X1 EQ/ EQ/ X7P=X7
    <- OPN-respects-EQ OP(X3,X4)=X7P EQ/ EQ/ X7P=X7 OP(X3,X4)=X7.

%worlds () (IOPN-associates-from-OPN-converse* IOP(X2,X4)=X6 IOP(X1,X6)=X7 IOP(X1,X2)=X3 
                                       %{=>}% OP(X3,X4)=X7).
%total {} (IOPN-associates-from-OPN-converse* _ _ _ _).

%{%
#ifdef IOP_TOTAL
%}%

%theorem IOPN-associates-from-OPN-converse :
	forall* {X1} {X2} {X4} {X6} {X7}
	forall {IOP2:IOPN X2 X4 X6} {IOP3:IOPN X1 X6 X7} 
        exists {X3} {IOP1:IOPN X1 X2 X3} {OP1:OPN X3 X4 X7} 
        true.

- : IOPN-associates-from-OPN-converse IOP(X2,X4)=X6 IOP(X1,X6)=X7 X3 IOP(X1,X2)=X3 OP(X3,X4)=X7
    <- IOPN-total IOP(X1,X2)=X3
    <- IOPN-associates-from-OPN-converse* IOP(X2,X4)=X6 IOP(X1,X6)=X7 IOP(X1,X2)=X3 OP(X3,X4)=X7.

%worlds () (IOPN-associates-from-OPN-converse IOP(X2,X4)=X6 IOP(X1,X6)=X7 
                                      %{=>}% X3 IOP(X1,X2)=X3 OP(X3,X4)=X7).
%total {} (IOPN-associates-from-OPN-converse _ _ _ _ _).

%{%
#endif
%}%

%theorem IOPN-associates-to-OPN* :
	forall* {X1} {X2} {X3} {X4} {X6} {X7}
	forall {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X3 X4 X7} {OP1:OPN X2 X4 X6} 
        exists {IOP3:IOPN X1 X6 X7}
        true.

- : IOPN-associates-to-OPN* OP(X3,X2)=X1 OP(X7,X4)=X3 OP(X2,X4)=X6 OP(X7,X6)=X1
    <- OPN-commutative OP(X2,X4)=X6 OP(X4,X2)=X6 
    <- OPN-associative* OP(X7,X4)=X3 OP(X3,X2)=X1 OP(X4,X2)=X6 OP(X7,X6)=X1.

%worlds () (IOPN-associates-to-OPN* IOP(X1,X2)=X3 IOP(X3,X4)=X7 OP(X2,X4)=X6 %{=>}% IOP(X1,X6)=X7).
%total {} (IOPN-associates-to-OPN* _ _ _ _).


%theorem IOPN-associates-to-OPN :
	forall* {X1} {X2} {X3} {X4} {X7}
	forall {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X3 X4 X7}
        exists {X6} {OP1:OPN X2 X4 X6} {IOP3:IOPN X1 X6 X7}
        true.

- : IOPN-associates-to-OPN OP(X3,X2)=X1 OP(X7,X4)=X3 X6 OP(X2,X4)=X6 OP(X7,X6)=X1
    <- OPN-associative OP(X7,X4)=X3 OP(X3,X2)=X1 X6 OP(X4,X2)=X6 OP(X7,X6)=X1
    <- OPN-commutative OP(X4,X2)=X6 OP(X2,X4)=X6.

%worlds () (IOPN-associates-to-OPN IOP(X1,X2)=X3 IOP(X3,X4)=X7 X6 OP(X2,X4)=X6 IOP(X1,X6)=X7).
%total {} (IOPN-associates-to-OPN _ _ _ _ _).


%theorem IOPN-associates-to-OPN-converse* :
	forall* {X1} {X2} {X3} {X4} {X6} {X7}
        forall {OP1:OPN X2 X4 X6} {IOP3:IOPN X1 X6 X7} {IOP1:IOPN X1 X2 X3}
	exists {IOP2:IOPN X3 X4 X7} 
        true.

- : IOPN-associates-to-OPN-converse* OP(X2,X4)=X6 OP(X7,X6)=X1 OP(X3,X2)=X1 OP(X7,X4)=X3
    <- OPN-commutative OP(X2,X4)=X6 OP(X4,X2)=X6
    <- OPN-associative-converse OP(X4,X2)=X6 OP(X7,X6)=X1 X3P OP(X7,X4)=X3P X3P+X2=X1
    <- OPN-right-cancels X3P+X2=X1 OP(X3,X2)=X1 EQ/ EQ/ X3P=X3
    <- OPN-respects-EQ OP(X7,X4)=X3P EQ/ EQ/ X3P=X3 OP(X7,X4)=X3.

%worlds () (IOPN-associates-to-OPN-converse* OP(X2,X4)=X6 IOP(X1,X6)=X7 IOP(X1,X2)=X3 
                                     %{=>}% IOP(X3,X4)=X7).
%total {} (IOPN-associates-to-OPN-converse* _ _ _ _).


%theorem IOPN-associates-to-OPN-converse :
	forall* {X1} {X2} {X4} {X6} {X7}
        forall {OP1:OPN X2 X4 X6} {IOP3:IOPN X1 X6 X7} 
        exists {X3} {IOP1:IOPN X1 X2 X3} {IOP2:IOPN X3 X4 X7} 
        true.

- : IOPN-associates-to-OPN-converse OP(X2,X4)=X6 OP(X7,X6)=X1 X3 OP(X3,X2)=X1 OP(X7,X4)=X3
    <- OPN-commutative OP(X2,X4)=X6 OP(X4,X2)=X6
    <- OPN-associative-converse OP(X4,X2)=X6 OP(X7,X6)=X1 X3 OP(X7,X4)=X3 OP(X3,X2)=X1.

%worlds () (IOPN-associates-to-OPN-converse OP(X2,X4)=X6 IOP(X1,X6)=X7 
                                    %{=>}% X3 IOP(X1,X2)=X3 IOP(X3,X4)=X7).
%total {} (IOPN-associates-to-OPN-converse _ _ _ _ _).
