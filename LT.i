#define CMP(X,Y) X>Y
#define CMPN GT
#define RCMP(X,Y) X<Y
#define RCMPN LT
#include "RCMP.i"
#undef RCMPN
#undef RCMP
#undef CMPN
#undef CMP

%abbrev LT-anti-reflexive = GT-anti-reflexive.
