// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//Complete the following natural deduction proof.
//When you are finished, do a Logika check.
//Your file should say "Logika verified".


//(p → q) ∨ (p → r) ⊢ p → q ∨ r

@pure def hw4_prob2(p: B, q: B, r: B): Unit = {
  Deduce(
    ((p __>: q) | (p __>: r) ) |- ( (p __>: q | r ) )
      Proof(
      1 (  (p __>: q) | (p __>: r)    ) by Premise,
      2 SubProof(
        3 Assume(  p  ),
        4 SubProof(
          5 Assume (  p __>: q  ),
          6 (  q                ) by ImplyE(5, 3),
          7 (  q | r            ) by OrI1(6)
          //goal: q | r
        ),
        8 SubProof(
          9 Assume (  p __>: r  ),
          10 (  r               ) by ImplyE(9,3),
          11 (  q | r           ) by OrI2(10)
          //goal: q | r
        ),
        12 (  q | r             ) by OrE(1,4,8)
      ),
      13 (  p __>: q | r           ) by ImplyI(2)
    )
  )
}
