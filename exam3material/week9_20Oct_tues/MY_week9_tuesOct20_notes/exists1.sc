// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∀ x (Human(x) → Mortal(x)), ∃ x (Human(x)) ⊢ ∃ x (Mortal(x))

@pure def exists1[T](Human: T=>B @pure, Mortal: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (Human(x) __>: Mortal(x))),
      ∃((x: T) => Human(x))
    )
    |-
    (
      ∃((x: T) => Mortal(x))
    )
    Proof(
      1 ( ∀((x: T) => (Human(x) __>: Mortal(x))) ) by Premise,
      2 ( ∃((x: T) => Human(x)) ) by Premise,
      
      3 Let((a: T) => SubProof(
        4 Assume ( Human(a) ), 
        5 ( Human(a) __>: Mortal(a) ) by AllE[T](1), 
        6 ( Mortal(a) ) by ImplyE(5, 4), 
        7 ( ∃((x: T) => Mortal(x)) ) by ExistsI[T](6),

      )),
      8 ( ∃((x: T) => Mortal(x)) ) by ExistsE[T](2, 3),
      
    )
  )
}