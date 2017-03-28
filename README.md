# ANS-Forth-libraries
Minimalist libraries as extensions to ANS Forth

basicsinglext.4th 

Unsigned integer number theory:

isprime \ u -- flag

nextprime \ u -- p

primefactors \ u -- q1 q2 ... qn n

radical \ n -- r

totients \ n -- t
mobius \ n -- m
bigomega \ n -- b 
smallomega \ n -- s
legendre \ a p -- i
tau \ u -- n    The number of divisors of u
sigma \ u -- s  The sum of all divisors of u
choose \ n k -- nCk
sqrtf \ u -- floor
log~ \ n -- 1+log n
umin \ u1 u2 -- u
umax \ u1 u2 -- u
umod \ u q -- u(mod q)
ugcd \ u1 u2 -- u
u*mod \ u1 u2 u3 -- u1*u2(mod u3)
u**mod \ b a m -- b^a(mod m)
