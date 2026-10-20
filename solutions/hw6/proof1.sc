// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ n (child(n) ∨ adult(n)), ¬child(Jane) ⊢ adult(Jane)

@pure def proof1[T](child: T=>B @pure, adult: T=>B @pure, Jane: T): Unit = {
  Deduce(
    (
      ∀((n: T) => (child(n) | adult(n))),
      !adult(Jane)
    )
    |-
    (
      child(Jane)
    )
      Proof(
        1 (∀((n: T) => (child(n) | adult(n)))) by Premise,
        2 ( !adult(Jane) ) by Premise,
        3 (child(Jane) | adult(Jane)) by AllE[T](1),
        4 SubProof(
          5 Assume (child(Jane))
        ),
        6 SubProof(
          7 Assume (adult(Jane)),
          8 (F) by NegE(7, 2),
          9 (child(Jane)) by BottomE(8)
        ),
        10 (child(Jane)) by OrE(3, 4, 6)
    )
  )
}
