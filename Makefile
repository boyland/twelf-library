GEN = bool.elf nat.elf rat.elf rat0.elf set.elf natpair.elf \
      natvector.elf rat0vector.elf \
      map.elf map-export.elf multiset.elf

BSRC = bool.cpp bool-base.elf

NATSRC = nat-head.elf nat-base.elf nat-inv.elf nat-comp.elf nat-less.elf \
         nat-inv-comp.elf nat-inv-less.elf nat-divrem.elf nat-minmax.elf nat.cpp

NATPSRC = pair.elf natpair.cpp natpair-base.elf

RATSRC = rat-head.elf rat-base.elf rat-inv.elf rat-comp.elf rat-less.elf \
          rat-inv-comp.elf rat-inv-less.elf rat-eq.elf rat-leq.elf \
	rat-count.elf rat.cpp

RAT0SRC = rat0-base.elf rat0.cpp

VSRC = vector.elf

RAT0VSRC = rat0vector.cpp
NATVSRC = natvector.cpp

OPSRC = EQ.i GE.i LE.i LT.i NE.i RCMP.i RELN.i \
        OPN-assoc.i OPN-preserves-CMPN.i OPN-preserves-GE.i \
	OPN-preserves-NE.i OPN-preserves-RCMPN.i \
	OPN-inv.i OPN-inv-assoc.i OPN-inv-cancel.i OPN-inv-preserves-CMPN.i \
	distrib.i SUB-distrib.i nozero-MUL-right-factors-over-SUB.i \
	minmax.elf

MAP = map-head.elf map-base.elf
MAP_MORE = map-leq.elf map-join.elf map-meet.elf map-scale.elf map-domain.elf
MAPSRC = ${MAP} ${MAP_MORE}

SETSRC = set.cpp set-head.elf set-base.elf set-help.elf set-remove.elf \
         set-extra.elf set-redef.elf

MSETSRC = multiset.cpp multiset-head.elf multiset-base.elf multiset-help.elf \
          multiset-add.elf multiset-extra.elf multiset-redef.elf

CLEANFILES = ${GEN} *.tgz tmp.elf

SOURCE = std.elf ${BSRC} ${NATSRC} ${NATPSRC} ${RATSRC} ${RAT0SRC} ${OPSRC} \
	${MAPSRC} ${SETSRC} ${MSETSRC} ${RAT0VSRC} ${NATVSRC} ${VSRC} \
	Makefile ${GN} ${REC} README

.PHONY: output
output : std.elf ${GEN}

.PHONY: clean realclean
clean :
	rm -f ${CLEANFILES}

CAT = cat
# The C preprocessor (not C++ compiler!)
CPP = cpp 
CPPFLAGS= -DBEGIN_ELF="%}%" -DEND_ELF="%{%"
REC = ./remove-empty-comments.pl
GN = ./get-names.pl

%.elf : %.cpp
	${CPP} ${CPPFLAGS} $*.cpp | ${REC} > $$$$.elf; \
	${GN} $* $$$$.elf | ${CAT} $$$$.elf - > $*.elf; \
	rm $$$$.elf

bool.elf : ${BSRC} EQ.i RELN.i

nat.elf : ${NATSRC} ${OPSRC}

natpair.elf : ${NATPSRC} EQ.i RELN.i

rat.elf : ${RATSRC} ${OPSRC}

rat0.elf : ${RAT0SRC} ${OPSRC}

rat0vector.elf : ${RAT0VSRC} ${VSRC}

natvector.elf : ${NATVSRC} ${VSRC}

map.elf : ${MAP} map-export.elf
	${CAT} ${MAP} map-export.elf > map.elf

map-export.elf : ${MAP}
	${GN} MAP ${MAP} > map-export.elf

map-leq-export.elf : map-leq.elf
	${GN} MAP map-leq.elf > map-leq-export.elf

set.elf : ${SETSRC} ${MAPSRC}

multiset.elf : ${MSETSRC} ${MAPSRC}

# Distribution:

DIST = www/.
DISTELF = std.elf bool.elf pair.elf \
            nat.elf natpair.elf rat.elf set.elf multiset.elf \
	    rat0.elf natvector.elf rat0vector.elf README

DISTFILES = ${DISTELF} map.elf \
            library.tgz map.tgz source.tgz

library.tgz : sources.cfg ${DISTELF}
	tar cvf - sources.cfg ${DISTELF} | gzip > $@

map.tgz : ${MAP} ${MAP_MORE}
	tar cvf - ${MAP} ${MAP_MORE} | gzip > map.tgz

source.tgz : ${SOURCE}
	tar cvf - ${SOURCE} | gzip > source.tgz

.PHONY: install
install : ${DISTFILES}
	cp ${DISTFILES} ${DIST}

checkin :
	/afs/cs.uwm.edu/users/csfac/boyland/cmd/vci -u ${SOURCE}
checkout :
	co ${SOURCE}

realclean : clean
	rm -f *~
	rcsclean
