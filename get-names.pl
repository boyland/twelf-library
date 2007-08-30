#!/usr/bin/perl -w

$module = $ARGV[0] . '`';
shift @ARGV;

foreach $f (@ARGV) {
  open (ELF,"<".$f) || die ("Could not open $f for reading.\n");
  while (<ELF>) {
    if (/^\%\{\% *$/) {
      while (<ELF>) {
        last if (/^\%\}\% *$/);
      }
      next;
    }
    s/// if (/%theorem /);
    s/// if (/%abbrev /);
    next if (/^[# %\t]/);
    next if (/^-/);
    next if (/^$/);
    s/[: ].*//;
    next if (/\`/);
    s/(.*)/%abbrev $module$1 = $1./;
    print $_;
  }
  close (ELF);
}
