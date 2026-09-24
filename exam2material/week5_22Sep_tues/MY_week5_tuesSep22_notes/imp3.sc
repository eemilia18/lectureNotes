// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def imply3(p: B, q: B, r: B): Unit = {
  Deduce(
    (p __>: (q __>: r)) |- ( (p __>: q) __>: (p __>: r)  )
      Proof(
      1 (  p __>: (q __>: r) ) by Premise,
      2 SubProof(
        3 Assume (p __>: q), //assume LHS of goal implies

        4 SubProof(
          5 Assume (p), //LHS of goal implies
          6 ( q __>: r ) by ImplyE(1, 5),
          7 ( q ) by ImplyE(3, 5),
          8 ( r ) by ImplyE(6, 7)

          //goal: r, RHS of goal implies
        ),
        9 ( p __>: r) by ImplyI(4)

        //nest implyi to create p __>: r
        //goal: RHS of implies, p __>: r
      ),
      10 ( (p __>: q) __>: (p __>: r) ) by ImplyI(2)

      //goal is implies: (p __>: q) __>: (p __>: r) 

    )
  )
}