// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ x (candy(x) → sweet(x)), ∀ x (sweet(x) → hasSugar(x)) ⊢ ∀ x (¬hasSugar(x) __>: ¬candy(x))

@pure def proof3[T](candy: T=>B @pure, sweet: T=>B @pure, hasSugar: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (candy(x) __>: sweet(x))),
      ∀((x: T) => (sweet(x) __>: hasSugar(x)))
    )
      |-
      (
        ∀((x: T) => (!hasSugar(x) __>: !candy(x))),
      )
      Proof(
        1 (  ∀((x: T) => (candy(x) __>: sweet(x)))        ) by Premise,
        2 (  ∀((x: T) => (sweet(x) __>: hasSugar(x)))     ) by Premise,
        3 Let ((a: T) => SubProof(
          4 SubProof(
            5 Assume(  !hasSugar(a)  ),
            6 SubProof(
              7 Assume(  candy(a)  ),
              8 (  candy(a) __>: sweet(a)                 ) by AllE[T](1),
              9 (  sweet(a) __>: hasSugar(a)              ) by AllE[T](2),
              10 (  sweet(a)                           ) by ImplyE(8, 7),
              11 (  hasSugar(a)                        ) by ImplyE(9, 10),
              12 (  F                                  ) by NegE(11, 5)
              //goal: F
            ),
            13 (  !candy(a)                            ) by NegI(6)
            
            //goal: !candy(a)
          ),
          14 (  !hasSugar(a) __>: !candy(a)               ) by ImplyI(4)
          //goal: !hasSugar(a) __>: !candy(a)
        )),
        15 (  ∀((x: T) => (!hasSugar(x) __>: !candy(x)))  ) by AllI[T](3)
    )
  )
}
