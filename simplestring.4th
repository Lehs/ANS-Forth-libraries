\ String extensions

: c+! \ c ad -- 
  tuck c@ + swap c! ;
\ add c to the byte at ad

: c1+! \ ad -- 
  1 swap c+! ;
\ add 1 to the byte at ad

: string! \ ad n addr -- 
  >r dup r@ c! r> 1+ swap move ;
\ store string ad n as counted string at addr

: string& \ ad n cadr -- 
  >r tuck         \ n ad n 
  r@ count + swap \ n ad cad' n
  move            \ n
  r> c+! ; 
\ concatenate string ad n to counted string at addr

: char& \ ch cad -- 
  tuck count + c! c1+! ;
\ concatenate character to counted string at cad

: space& \ cad -- 
  bl swap char& ;
\ concatenate space to counted string at cad

: unum& \ u cad -- 
  swap 0 <# #s #> rot string& ;
\ concatenate unsigned number at counted string at cad

: num& \ n cad -- 
  swap dup abs 0 <# #s rot sign #> rot string& ;
\ concatenate signed number to counted string at cad

: dnum& \ d cad -- 
  -rot dup -rot dabs <# #s rot sign #> rot string& ;
\ concatenate double signed number to counted string at cad

: udnum& \ ud cad -- 
  -rot <# #s #> rot string& ;
\ concatenate double unsigned number to counted string at cad

