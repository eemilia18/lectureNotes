// #Sireum #Logika
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

/*
Use natural deduction to prove that the following two statements are equivalent:
    ¬(p → q)
    p ∧ ¬q

You will need to complete the two proofs below. When you
are finished, run a Logika check. Your file should
say "Logika verified"
*/

@pure def hw4_prob7_part1(p: B, q: B): Unit = {
  Deduce(
    ( !(p __>: q) ) |-  ( p & !q )
      Proof(
        1 (  !(p __>: q)              ) by Premise,
        2 SubProof(
          3 Assume(  !(p & !q)  ),
          4 SubProof(
            5 Assume(  p  ),
            6 SubProof(
              7 Assume(  !q  ),
              8 (  p & !q          ) by AndI(5,7),
              9 (  F               ) by NegE(8, 3)

              //goal: contradiction
            ),
            10 (  q                ) by PbC(6)
            //Goal: q, for p->q
          ),
          11 (  p __>: q              ) by ImplyI(4),
          12 (  F                  ) by NegE(11, 1)

          //Goal: contradiction
        ),
        13 (  p & !q               ) by PbC(2)
    )
  )
}

@pure def hw4_prob7_part2(p: B, q: B): Unit = {
  Deduce(
    ( p & !q ) |-  ( !(p __>: q) )
      Proof(
      1 (  p & !q            ) by Premise,
      2 (  p                 ) by AndE1(1),
      3 (  !q                ) by AndE2(1),
      4 SubProof(
        5 Assume(  p __>: q  ),
        6 (  q               ) by ImplyE(5, 2),
        7 (  F               ) by NegE(6, 3)
        //goal: contradiction
      ),
      8 (  !(p __>: q)          ) by NegI(4)
    )
  )
}
