---- MODULE DieHard ----
EXTENDS Integers

VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Init == /\ big = 0
        /\ small = 0

FillSmall == /\ small' = 3
             /\ big' = big

FillBig == /\ big' = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ big' = 0
            /\ small' = small


SmallToBig == IF big + small <= 5
              THEN /\ big' = big + small
                   /\ small' = 0
              ELSE /\ big' = 5
                   /\ small' = small - (5 - big)

BigToSmall == IF small + big <= 3
              THEN  /\ small' = small + big
                    /\ big' = 0
              ELSE  /\  small' = 3
                    /\ big' = big - (3 - small)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall
====

Notice that the Init is a bunch of conjuncts
while Next is a bunch of disjuncts!