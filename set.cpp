#include "set-head.elf"
%{%
#define data unit
#define join union
#define meet intersection
#define domain member
#define fresh not-member
%}%
#include "set-help.elf"
#include "set-base.elf"
#include "set-extra.elf"
#include "set-redef.elf"
#include "set-remove.elf"
