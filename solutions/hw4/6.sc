// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

/*
Use natural deduction to prove that the following two statements are equivalent:
    p → q
    ¬p ∨ q

You will need to complete the two proofs below. When you
are finished, run a Logika check. Your file should
say "Logika verified"
*/

@pure def hw4_prob6_part1(p: B, q: B): Unit = {
  Deduce(
    ( p __>: q ) |-  ( !p | q )
      Proof(
        1 (  p __>: q                  ) by Premise,
        2 SubProof(
          3 Assume (  !(!p | q)  ),
          4 SubProof(
            5 Assume(  !p  ),
            6 (  !p | q             ) by OrI1(5),
            7 (  F                  ) by NegE(6, 3),

            //Goal: contradiction
          ),
          8 (  p                    ) by PbC(4),
          9 (  q                    ) by ImplyE(1, 8),
          10 (  !p | q              ) by OrI2(9),
          11 (  F                   ) by NegE(10, 3)

          //Goal: contradiction
        ),
      12 (  !p | q                  ) by PbC(2)
    )
  )
}

@pure def hw4_prob6_part2(p: B, q: B): Unit = {
  Deduce(
    //@formatter: off

    ( !p | q ) |-  ( p __>: q )
      Proof(
        1 (  !p | q           ) by Premise,
        2 SubProof(
          3 Assume(  p  ),
          4 SubProof(
            5 Assume(  !p  ),
            6 (  F            ) by NegE(3, 5),
            7 (  q            ) by BottomE(6)

            //goal: contradiction
            //goal: q
          ),
          8 SubProof(
            9 Assume(  q  ),

            //goal: q
          ),
          10 (  q             ) by OrE(1, 4, 8)

          //goal: q
        ),
      11 (  p __>: q             ) by ImplyI(2)
    )
    //@formatter:on
  )
}
