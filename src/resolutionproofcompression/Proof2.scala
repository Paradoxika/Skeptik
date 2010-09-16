/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import resolutionproofcompression.ResolutionCalculus._


object Proof2 {
  val p = true
  val n = false

  val pK7 = Input(L("b", n)::L("a",n)::L("g",p)::Nil)
  val pK1 = Input(L("a",p)::Nil)
  val pK2 = Input(L("b",p)::Nil)

  val pD = Resolvent(Resolvent(pK2,
                               Resolvent(pK1,
                                         Resolvent(Input(L("g",n)::L("c",p)::Nil),
                                                   pK7))),
                     Input(L("c",n)::L("d",p)::Nil))

  val clempty = Resolvent(Resolvent(Resolvent(Resolvent(Resolvent(Input(L("g",n)::L("e",n)::L("f",p)::Nil),
                                                                pK7),
                                                      pK1),
                                            pK2),
                                  Resolvent(Input(L("d",n)::L("f",n)::Nil),
                                            pD)),
                        Resolvent(Input(L("d",n)::L("e",p)::Nil),
                                  pD))
}
