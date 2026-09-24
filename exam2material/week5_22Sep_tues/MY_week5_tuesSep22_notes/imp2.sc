// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def imply2(p: B, q: B, r: B): Unit = {
  Deduce(
    (p __>: r, q __>: r ) |- ( p | q __>: r  )
      Proof(
      1 (  p __>: r   ) by Premise,
      2 (  q __>: r   ) by Premise,

      //use ImplyI to introduce goal implies
      3 SubProof(
        4 Assume ( p | q ), //LHS of implies

        //use OrE on p | q to get r in both cases
        5 SubProof(
          6 Assume(p),
          7 ( r ) by ImplyE(1, 6)

          //goal: r
        ),
        8 SubProof(
          9 Assume ( q ),
          10 ( r ) by ImplyE(2, 9)
        ),
        11 ( r ) by OrE(4, 5, 8)

        //goal: r (RHS of implies)
      ),
      12 ( p | q __>: r) by ImplyI(3)

      //goal is an implies statement, p | q __>: r 

    )
  )
}