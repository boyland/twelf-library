#!/usr/bin/perl -w
# Remove empty twelf comments from standard input files.
# We also remove CPP stuff.
  $init = 1;
  while (<>) {
    next if ($init && /^$/);
    next if (/^\#/);
    $init = 0;
    if (/^\%\{\% *$/) {
      $buffer = $_;
      $print = 0;
      while (<>) {
	next if (/^\#/);
        $buffer .= $_;
        last if (/^\%\}\% *$/);
        next if (/^ *$/);
        $print = 1;
      }
      print $buffer if ($print);
      next;
    }
    print $_;
  }

