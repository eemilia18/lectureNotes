// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ n (child(n) ∨ adult(n)), ∀ n (¬adult(n)) ⊢ ∀ n (child(n))

@pure def proof2[T](child: T=>B @pure, adult: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((n: T) => (child(n) | adult(n))),
      ∀((n: T) => !adult(n))
    )
      |-
      (
        ∀((n: T) => child(n))
      )
      Proof(
        1 (∀((n: T) => (child(n) | adult(n)))) by Premise,
        2 ( ∀((n: T) => !adult(n)) ) by Premise,
        3 Let ((random: T) => SubProof(
            4 (child(random) | adult(random)) by AllE[T](1),
            5 (!adult(random)) by AllE[T](2) ,
            6 SubProof(
                7 Assume(child(random))
            ),
            8 SubProof(
              9 Assume(adult(random)),
              10 (F) by NegE(9, 5),
              11 (child(random)) by BottomE(10)
            ),
            12 (child(random)) by OrE(4, 6, 8)
        )),
        13 (∀((n: T) => child(n))) by AllI[T](3)
      )
  )
}
