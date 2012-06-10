package skeptik;

import skeptik.algorithm.generator.formulaGen._;

import scala.collection.immutable.{ HashSet => ISet };
import org.specs2.mutable._;
import org.junit.runner.RunWith;
import org.specs2.runner.JUnitRunner;

@RunWith(classOf[JUnitRunner])
class FormulaTest extends SpecificationWithJUnit {

  "Formula generator" should {
    "produce 47 items for (2,4)" in {
      val goals = generate2(2, 4)
      goals must have length 47
    }
    "produce 58 items for (2,5)" in {
      val goals = generate2(2, 5)
      goals must have length 58
    }
  }
}
