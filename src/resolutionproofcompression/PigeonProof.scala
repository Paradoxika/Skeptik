/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import resolutionproofcompression.ResolutionCalculus._

object PigeonProof {
  val p = true
  val n = false

  val phi1 = Input(List(L("p11",p),L("p12",p)))
  val phi2 = Input(List(L("p21",p),L("p22",p)))
  val phi3 = Input(List(L("p31",p),L("p32",p)))

  val clempty = Resolvent(Resolvent(Resolvent(Resolvent(Resolvent(Resolvent(Resolvent(phi2,
                                                                                             Input(List(L("p21",n),L("p31",n)))),
                                                                                   phi3),
                                                                         Input(List(L("p32",n),L("p12",n)))),
                                                               phi1),
                                                     Input(List(L("p11",n),L("p21",n)))),
                                           phi2),
                                 Resolvent(Resolvent(phi3,
                                                     Resolvent(Resolvent(Input(List(L("p12",n),L("p22",n))),
                                                                         phi1),
                                                               Input(List(L("p31",n),L("p11",n))))),
                                           Input(List(L("p22",n),L("p32",n)))))
}

object Proof5 {
  val p = true
  val n = false

  val cl1 = Input(List(L("v1",p),L("v2",p),L("v3",p)))
  val cl2 = Input(List(L("v1",n),L("v2",p),L("v3",p)))
  val cl3 = Input(List(L("v1",p),L("v2",n),L("v3",p)))
  val cl4 = Input(List(L("v1",n),L("v2",n),L("v3",p)))
  val cl5 = Input(List(L("v1",p),L("v2",p),L("v3",n)))
  val cl6 = Input(List(L("v1",n),L("v2",p),L("v3",n)))
  val cl7 = Input(List(L("v1",p),L("v2",n),L("v3",n)))
  val cl8 = Input(List(L("v1",n),L("v2",n),L("v3",n)))
  val cl9 = Resolvent(cl3,cl1)
  val cl10 = Resolvent(Resolvent(cl7,cl5),cl9)
  val cl11 = Resolvent(Resolvent(cl8,cl4),cl10)
  val cl12 = Resolvent(Resolvent(cl2,cl11),cl10)
  val cl13 = Resolvent(Resolvent(Resolvent(cl6,cl11),cl10),cl12)
}
