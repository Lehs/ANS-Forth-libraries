\ alphabetic sets

s" nestedsets.4th" included
s" stringstack.4th" included

false [if]
Sets of strings on the string stack: a string starting with { and ending with } where
all element strings are separated by ','. Examples:

s {mon,thu,wed,thu,fri}"  ok
s {sat,sun}"  ok
sunion cr str.
{mon,thu,wed,thu,fri,sat,sun}  ok

sintersection \ s1 s2 -- s3
sdiff \ s1 s2 -- s3
smember \ string set -- flag
ssubset \ s1 s2 -- flag
sequal \ s1 s2 -- flag
scard \ set -- n

More information on https://forthmath.blogspot.se
[then]

\ Create string of set or ordered sequence
: set>str \ set -- string   
  snull foreach over >r
  do zst> loop r> 0
  do schr& loop ;

: str>seq \ string -- sequence
  ( sduplen 1+ 1
  do i stopad c@
  loop ) sdrop ;

: seq>set \ seq -- set
  zst> 1+ >zst
  set-sort reduce ;

\ {(104,101,106),(100,117),(103,108,97,100,101)}
: z>s \ seq -- str
  snull s{& zst@
  if foreach
     do set>str s& s,& 
     loop str> 1- >str
  else zdrop 
  then s}& ;

: revseqset \ s -- s'
  zdup cardinality
  zst xst setmove
  xst> swap 0
  do xst zst setmove
  loop >zst ;

\ s {hello there,all together,sentence}"
: s>z \ string -- set
  str@ nip 2 = if sdrop 0 >zst exit then
  str> 1 /string 1- >str
  snull s,& sswap {
  begin sanalyze
  while snip sswap str>seq
  repeat str>seq } sdrop 
  revseqset ;

\ union of stringsets
: sunion \ s1 s2 -- s3
  s>z s>z union z>s ;

: sintersection \ s1 s2 -- s3
  s>z s>z intersection z>s ;

: sdiff \ s1 s2 -- s3
  s>z s>z zswap diff z>s ;
\ s3 is the set of elements in s1 which not occure in s2

: smember \ string set -- flag
  s>z
  str>seq 
  zswap member ;

: ssubset \ s1 s2 -- flag
  s>z s>z zswap subset ;

: sequal \ s1 s2 -- flag
  s>z s>z zet= ;

: scard \ set -- numb of elements
  s>z cardinality ;
