\ String stack
false [if]
s Hello world!"
s This is String Stack"
sswap str. space str.

sdrop sdup sswap sover srot spick snip stuck 
s& \ s1 s2 -- s1&s2
sempty \ -- flag
[then]
: clearbuf \ ad --
  dup cell+ swap ! ;

variable stp

0x4000 constant stlim
stlim allocate throw dup constant stbuf clearbuf
\ ascii buffer, at stbuf is loaded address to first free byte

0x1000 constant stalim
stalim allocate throw dup constant staddr clearbuf
\ address buffer, at staddr is loaded address to first free cell

: clstr  0 stp ! stbuf clearbuf staddr clearbuf ;

: >str \ ad n --    put string on stack
  tuck             \ n ad n
  stbuf @ dup      \ n ad n a a
  staddr @ !       \ n ad n a
  cell staddr +!
  swap move        \ n
  stbuf +!
  1 stp +! ;

: str@ \ -- ad n
  stp @ cells staddr + @
  dup stbuf @ swap - ;

: str> \ -- ad n
  str@ over stbuf !
  cell negate staddr +!
  -1 stp +! ;

: sempty \ -- flag
  stp @ 0= ;

\ addr to the ith string from the bottom of the stack
: ist@ \ i -- ad n     i=1,...
  dup stp @ =
  if cells staddr + @ dup stbuf
  else cells staddr + dup @ dup rot cell+
  then @ swap - ;

\ addr to the kth string from the top of the stack
: spickad \ k -- ad n
  stp @ swap - ist@ ;

\ print string stack
: .str stp @ 0 ?do cr i spickad type loop ;

: str. str> type ;

\ enter string from commando line
: s [char] " parse >str ;
\ use s" example" >str in definitions

: sdup stp @ ist@ >str ;
: sdrop str> 2drop ;
: sover stp @ 1- ist@ >str ;
: soover stp @ 2 - ist@ >str ;
: snip str> sdrop >str ;
: sswap sover str> str> sdrop >str >str ;
: srot soover str> str> str> sdrop >str >str >str ;
: stuck sswap sover ;
: spick spickad >str ;

: s& \ s1 s2 -- s1&s2
  -1 stp +!
  staddr @ @
  cell negate staddr +!
  staddr @ ! ;

: clearstrstack \ --
  begin sempty 0=
  while sdrop
  repeat ;

\ lenghth of top string
: sduplen \ s -- s | -- n
  str@ nip ;

\ length of second string
: soverlen \ s1 s2 -- s1 s2 | -- n
  1 spickad nip ;

\ the n leftmost chars in string
: sleft \ s -- s' | n --
  str> drop swap >str ;

\ the n rightmost chars in string
: sright \ s -- s' | n --
  str> rot over swap - /string >str ;

\ split the string after the nth letter
: ssplit \ s -- s' s" | n --
  sdup dup sleft sswap
  sduplen swap - sright ;

\ the address to the jth letter in top string
: stopad \ s1 s2 -- s1 s2 | j -- adj    (in s2) j>0
  str@ drop 1- + ;

\ the address to the ith letter in second string
: ssecad \ s1 s2 -- s1 s2 | i -- adi
  1 spickad drop 1- + ;

\ split s2 if s1 is a part of s2 (true flag)
\ true -> s2=s3&s1&s4
: sanalyze \ s1 s2 -- s1 s3 s1 s4 / s2 | -- flag
  soverlen                   \ m
  str@ 1 spickad search      \ m ad n f
  if nip sduplen swap -      \ m k-n
     ssplit                  \ m
     ssplit true
  else 2drop drop false
  then ;

\ check if s1 is in s2
: substring \ s1 s2 -- s1 s2 | -- flag
  str@ 1 spickad search nip nip ;

\ replace s2 with s1 wherever in s3
: sreplace \ s1 s2 s3 -- s4
  begin sanalyze
  while snip 3 spick sswap s& s&
  repeat snip snip ;

\ string comparison
: scomp \ s1 s2 -- | -- n    -1:s1>s2, +1:s1<s2, 0:s1=s2
  str> str> 2swap compare ;

\ put an empty string on the stack
: snull pad 0 >str ;

\ conc. signs to top string on stack
: schr& \ s -- s' | ch --
  >r str> 2dup + r> swap c! 1+ >str ;

: sbl& bl schr& ;
: s,& [char] , schr& ;
: s.& [char] . schr& ;
: s;& [char] ; schr& ;
: s:& [char] : schr& ;
: s?& [char] ? schr& ;
: s!& [char] ! schr& ;
: s-& [char] - schr& ;
: s|& [char] | schr& ;
: s{& [char] { schr& ;
: s}& [char] } schr& ;

\ same length?
: slen= \ s1 s2 -- | -- flag
  str> nip str> nip = ;

\ remove ending spaces
: strail \ s -- s'
  str@ -trailing ;

: >capital \ ch -- ch'
  [char] _ and ;

: >common \ ch -- ch'
  [char] ` or ;

: capital \ ch --flag
  [char] A [char] Z 1+ within ;

: common \ ch -- flag
  [char] a [char] z 1+ within ;

\ lower letters, eng.
: slower \ s -- s'
  str@ over + swap
  do i c@ capital
     if i c@ >common i c! then
  loop ;

\ upper letters, eng.
: supper \ s -- s'
  str@ over + swap
  do i c@ common
     if i c@ >capital i c! then
  loop ;

\ Unsigned double from string
: str>ud \ s -- s' | -- ud flag
  0. str@ dup >r >number dup >r >str snip 2r> > ;

\ Double from string
: str>d \ s -- s' | -- d flag
  1 stopad c@ [char] - = dup
  if sduplen 1- sright
  then str>ud >r rot if dnegate then r> ;

: snobl \ s -- s'      remove all blanks
  snull snull sbl& srot
  sreplace ;

: sjustabc \ s -- s'   remove all signs but eng. letters
  sduplen 1+ 1
  do i stopad c@ dup common swap capital or 0=
     if bl i stopad c! then
  loop snobl ;

\ bioinformatics --------------

\ Hamming distance
: hamming \ s1 s2 -- s1 s2 | -- n
  0 1 spickad drop str@ 0
  do over i + c@
     over i + c@ = 0=
     if rot 1+ -rot then
  loop 2drop ;

\ Wagner-Fischer algorithm

: distad \ s1 s2 -- s1 s2 | i j -- addr
  soverlen 1+ * + cells pad + ;

: distinit \ s1 s2 -- s1 s2
  soverlen 1+ 0 do i i 0 distad ! loop
  sduplen 1+ 0 do i 0 i distad ! loop ;

\ Levenshtein distance
: editdistance \ s1 s2 -- s1 s2 | -- lev
  distinit sduplen 1+ 1
  do soverlen 1+ 1
     do i ssecad c@ j stopad c@ =
        if i 1- j 1- distad @
        else i 1- j distad @ 1+              \ a deletion
             i j 1- distad @ 1+              \ an insertion
             i 1- j 1- distad @ 1+           \ a substitution
             min min
        then i j distad !
     loop
  loop soverlen sduplen distad @ ;
