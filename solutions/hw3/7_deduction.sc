// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//Complete the following natural deduction proof.
//When you are finished, your file should say "Logika verified".

//(p ∧ q) ∨ (q ∧ r) ⊢  q ∧ (r ∨ p)


@pure def deduction6(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    ((p & q) | (q & r)) |- (q & (r | p))
      Proof(
      1 (  (p & q) | (q & r)  ) by Premise,
      2 SubProof(
        3 Assume(  p & q  ),
        4 (  p                ) by AndE1(3),
        5 (  q                ) by AndE2(3),
        6 (  r | p            ) by OrI2(4),
        7 (  q & (r | p)      ) by AndI(5, 6)
      ),
      8 SubProof(
        9 Assume (  q & r  ),
        10 (  q               ) by AndE1(9),
        11 (  r               ) by AndE2(9),
        12 (  r | p           ) by OrI1(11),
        13 (  q & (r | p)     ) by AndI(10, 12)
      ),
      14 (  q & (r | p)       ) by OrE(1,2,8)
    )
    //@formatter:on
  )
}