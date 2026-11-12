// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∃ x (ksu(x) ∨ ku(x)), ¬(∃ x ku(x)) ⊢ ∃ x ksu(x)

@pure def proof1[T](ksu: T=>B @pure, ku: T=>B @pure): Unit = {
  Deduce(
    (
      ∃((x: T) => (ksu(x) | ku(x))),
      !(∃((x: T) => ku(x)))
      )
      |-
      (
        ∃((x: T) => ksu(x))
        )
      Proof(
        1 (  ∃((x: T) => (ksu(x) | ku(x)))      ) by Premise,
        2 (  !(∃((x: T) => ku(x)))              ) by Premise,
        3 Let ((alias: T) => SubProof(
          4 Assume(  ksu(alias) | ku(alias)  ),
          5 SubProof(
            6 Assume(  ksu(alias)  ),
            7 (  ∃((x: T) => ksu(x))            ) by ExistsI[T](6)
            //goal: ∃((x: T) => ksu(x))
          ),
          8 SubProof(
            9 Assume(  ku(alias)  ),
            10 (  ∃((x: T) => ku(x))            ) by ExistsI[T](9),
            11 (  F                             ) by NegE(10, 2),
            12 (  ∃((x: T) => ksu(x))           ) by BottomE(11)

            //goal: ∃((x: T) => ksu(x))
          ),
          13 (  ∃((x: T) => ksu(x))             ) by OrE(4, 5, 8)
          
          //goal: ∃((x: T) => ksu(x))
        )),
      14 (  ∃((x: T) => ksu(x))                 ) by ExistsE[T](1, 3)
    )
  )
}
