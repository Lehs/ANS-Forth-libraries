\ Preparation for SP-Forth

REQUIRE case-ins lib/ext/caseins.f
REQUIRE LOCALS| ~af/lib/locals-ans.f
REQUIRE { lib/ext/locals.f
REQUIRE M*/ lib/include/double.f
REQUIRE F. lib/include/float2.f
REQUIRE /STRING lib/include/string.f
REQUIRE INCLUDED devel/~ygrek/spf/included.f

: <= > 0= ;
: >= < 0= ;

CASE-INS ON

WINAPI: GetTickCount KERNEL32.DLL
WINAPI: SetConsoleCursorPosition KERNEL32.DLL
WINAPI: GetConsoleScreenBufferInfo KERNEL32.DLL
WINAPI: FillConsoleOutputCharacterA KERNEL32.DLL

 0 2 -- off_x
   2 -- off_y
   CONSTANT /coord

 0 2 -- Left
   2 -- Top
   2 -- Right
   2 -- Bottom
   CONSTANT /rect

 0 /coord -- Size
   /coord -- Position
        2 -- Attrib
   /rect  -- Window
   /coord -- Dimensions
   CONSTANT /buffer

CREATE buffer /buffer ALLOT

: xy@ \ addr -- x y
  DUP off_x W@ SWAP off_y W@ ;

: GETXY \ -- x y 
  buffer H-STDOUT GetConsoleScreenBufferInfo DROP
  buffer Position xy@ ;

: SETXY \ x y --
  16 LSHIFT OR H-STDOUT SetConsoleCursorPosition DROP ;

: ~chars \ char # --
  SP@ GETXY 16 LSHIFT OR 2SWAP SWAP H-STDOUT
  FillConsoleOutputCharacterA DROP ;

: PAGE  0 0 SETXY BL 
  buffer H-STDOUT GetConsoleScreenBufferInfo DROP
  buffer Size ~chars ;

\ : fround 1.e 2.e f/ f+ fint ;
: utime  GetTickCount 1000 um* ;
: under+  rot + swap ;

: .r \ n i --
  >r dup 0< swap abs
  0 <# #S rot sign #>
  R> OVER - SPACES TYPE ;

\ CASE-OF STRUCTURE

: CASE  \ -- 0 
  0 ; IMMEDIATE \ initial count of ofs 

: OF \ c: #of -- orig #of+1 
     \ x --  
  1+ >R 
  POSTPONE OVER 
  POSTPONE = 
  [COMPILE] IF 
  POSTPONE DROP 
  R> ; IMMEDIATE 

: ENDOF \ c: orig1 #of -- orig2 #of  
  >R [COMPILE] ELSE R> ; IMMEDIATE 

: ENDCASE \ c: orig1..orign #of --  
  POSTPONE drop \ discard case value 
  0 ?DO [COMPILE] THEN LOOP ; IMMEDIATE \ generate targets 

: f>s f>d drop ;
: s>f 0 d>f ;

: OK2 ( -- ) STATE @ IF EXIT THEN ."  ok" CR ; 
' OK2 TO OK

\ _SYSTEMTIME
0
2 -- wYear
2 -- wMonth
2 -- wDayOfWeek
2 -- wDay
2 -- wHour
2 -- wMinute
2 -- wSecond
2 -- wMilliseconds
CONSTANT /SYSTEMTIME
CREATE SYSTEMTIME /SYSTEMTIME ALLOT

WINAPI: GetLocalTime KERNEL32.DLL
\ WINAPI: GetTickCount KERNEL32.DLL

: TIME&DATE \ -- sec min hr day mt year 
  SYSTEMTIME GetLocalTime DROP
  SYSTEMTIME wSecond W@
  SYSTEMTIME wMinute W@
  SYSTEMTIME wHour W@
  SYSTEMTIME wDay W@
  SYSTEMTIME wMonth W@
  SYSTEMTIME wYear W@
;
