#define data nat
#define DATA_NE 1
#undef DATA_ARITH
#define DATA_ZERO 1
 %abbrev nat`zero = nat`z.
#include "vector.elf"



%%%% Renamings



%abbrev natvector = vector.


%abbrev natvector/0 = vector/0.


%abbrev natvector/+ = vector/+.



%%%% Exports


