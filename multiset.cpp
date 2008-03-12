#include "multiset-head.elf"
%{%
#define data nat
#define join union
#define meet intersection
#define domain member
#define fresh not-member
%}%
#include "multiset-help.elf"
#include "multiset-base.elf"
#include "multiset-extra.elf"
 /* #include "multiset-add.elf" */
#include "multiset-redef.elf"

