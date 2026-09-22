// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//Complete the following natural deduction proof.
//When you are finished, your file should say "Logika verified".

//p ∨ q ∨ r ⊢ r ∨ q ∨ p


@pure def deduction6(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    (p | q | r) |- (r | q | p)
      Proof(
      1 (  p | q | r         ) by Premise,
      2 SubProof(
        3 Assume(  p | q  ),
        4 SubProof(
          5 Assume(  p  ),
          6 (  r | q | p     ) by OrI2(5)
        ),
        7 SubProof(
          8 Assume(  q  ),
          9 (  r | q         ) by OrI2(8),
          10 (  r | q | p    ) by OrI1(9)
        ),
        11 (  r | q | p      ) by OrE(3,4,7)
      ),
      12 SubProof(
        13 Assume(  r  ),
        14 (  r | q          ) by OrI1(13),
        15 (  r | q | p      ) by OrI1(14)
      ),
      16 (  r | q | p        ) by OrE(1,2,12)
    )
    //@formatter:on
  )
}