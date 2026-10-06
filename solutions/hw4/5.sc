// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//Complete the following natural deduction proof.
//When you are finished, do a Logika check.
//Your file should say "Logika verified."


//p → a ∨ b, a → d, q → ¬b, p ∧ q ⊢ d

@pure def hw4_prob5(p: B, a: B, b: B, q: B, d: B): Unit = {
  Deduce(
    ( p __>: a | b, a __>: d, q __>: !b, p & q ) |-  ( d )
      Proof(
      1 (  p __>: a | b      ) by Premise,
      2 (  a __>: d          ) by Premise,
      3 (  q __>: !b         ) by Premise,
      4 (  p & q          ) by Premise,
      5 (  p              ) by AndE1(4),
      6 (  q              ) by AndE2(4),
      7 (  a | b          ) by ImplyE(1, 5),
      8 (  !b             ) by ImplyE(3, 6),
      9 SubProof(
        10 Assume(  a  ),
        11 (  d           ) by ImplyE(2, 10)
        //goal: d
      ),
      12 SubProof(
        13 Assume(  b  ),
        14 (  F           ) by NegE(13, 8),
        15 (  d           ) by BottomE(14)
        //goal: d
      ),
      16 (  d             ) by OrE(7, 9, 12)
    )
  )
}
