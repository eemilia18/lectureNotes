// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ x (student(x) → csharp(x)), ∃ x ¬csharp(x) ⊢ ∃ x ¬student(x)

@pure def proof2[T](student: T=>B @pure, csharp: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (student(x) __>: csharp(x))),
      ∃((x: T) => !csharp(x))
    )
      |-
      (
        ∃((x: T) => !student(x))
        )
      Proof(
        1 (  ∀((x: T) => (student(x) __>: csharp(x)))  ) by Premise,
        2 (  ∃((x: T) => !csharp(x))                ) by Premise,
        3 Let ((alias: T) => SubProof(
          4 Assume(  !csharp(alias)  ),
          5 (  student(alias) __>: csharp(alias)       ) by AllE[T](1),
          6 SubProof(
            7 Assume(  student(alias)  ),
            8 (  csharp(alias)                      ) by ImplyE(5, 7),
            9 (  F                                  ) by NegE(8, 4)
            //goal: F
          ),
          10 (  !student(alias)                     ) by NegI(6),
          //goal: !student(alias)
          
          11 (  ∃((x: T) => !student(x))            ) by ExistsI[T](10)
          //goal: ∃((x: T) => !student(x))
        )),
        12 (  ∃((x: T) => !student(x))              ) by ExistsE[T](2, 3)
    )
  )
}
