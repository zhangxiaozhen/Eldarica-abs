/**
 * Copyright (c) 2011-2016 Philipp Ruemmer and Pavle Subotic.
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.abstractions

import scala.math.PartialOrdering
import ap.SimpleAPI
import ap.terfor.{ConstantTerm, OneTerm, TerForConvenience, Term, TermOrder}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.ReduceWithEqs
import ap.parser.{IBoolLit, IExpression, IFormula, ITerm, IVariable, InputAbsy2Internal}
import ap.util.{LRUCache, PeekIterator}
import ap.util.Timeout

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}
                //注:这里 =>是“重命名符”，重命名的格式为“原始名 => 新名”。这里引入了collection.mutabl中的子类(子成员)ArrayBuffer,BitSet, HashMap,HashSet,但是后三者被重命名成MBitSet,MHashMap,MHashSet了
               //因此，var a = MBitSet()，显示a的类型是BitSet，而不是MBitSet

/** 可变的Seq和Map(定义WaitList需要)属于新加的*/
//import scala.collection.mutable.Seq
//import scala.collection.mutable.Map

import scala.collection.immutable.BitSet
import scala.util.Random

// Defines an interface to lattices
trait AbsLattice
{
  type LatticeObject

  val latticeOrder : PartialOrdering[LatticeObject]   //top元素的序关系最大，其他元素的序关系都<它
  val top, bottom : LatticeObject
  val arity : Int

  /** Does the lattice only contain one element? */
  def isUnit : Boolean = (top == bottom)

  def pp(o : LatticeObject) : String

  def join(x: LatticeObject, y: LatticeObject): LatticeObject
  def meet(x: LatticeObject, y: LatticeObject): LatticeObject

  /** Compute the direct parents/successors of an object */
  def succ(x: LatticeObject): Iterator[LatticeObject]
  /** Compute the direct children/predecessors of an object */
  def pred(x: LatticeObject): Iterator[LatticeObject]
  /**
    * 此函数的作用是：以所输入的topEL为界来计算出另一个输入元素obj的后继元素
    */
  def succWithLimit(obj:LatticeObject, topEl:LatticeObject) : Iterator[LatticeObject]

  /** Compute the direct children/predecessors of an object,
    * with ascending cost. */
  def predCheapestFirst(x: LatticeObject): Iterator[LatticeObject]

  /** Compute the direct children/predecessors of an object,
    * in pseudo-random order. */
  def predRandom(x: LatticeObject)
                (implicit randGen : Random): Iterator[LatticeObject]

  /** A measure for the size of an object */
  def predNum(x: LatticeObject): Int
 
  /** Compute an element in between lower and upper */
  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) : LatticeObject

  /** Compute the cost of an object. Cost is monotonic, bigger objects have
      larger cost. */
  def cost(obj : LatticeObject) : Int

/*  def g(o: LatticeObject) : Int = {
    if (o == bottom)
      return 1;
    else
      g(succ) + 1;
  }*/
  /** Try to eliminate atomic parts of the object that have cost larger than
      bound. In general, <code>result <= obj</code>, and for all
      <code>x <= obj</code> such that <code>cost(x) <= bound</code>,
      we have <code>x <= result</code>. */
  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject

  /** Assuming that <code>infeasible < feasible</code>,
      return an object such that <code>feasible = join(infeasible, result)</code>,
      and such that, whenever <code>x <= elem</code>, and <code>x</code> feasible, 
      it holds that <code>x >= result</code>. */
  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject

  // Create the composed relation R_A[xa, x] \circ R_B[x, xb] 
  def asRelation(obj : LatticeObject,  xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula]

  // Create the relations 
  def asRelation(obj : LatticeObject,  xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], 
                 xb : Seq[Seq[ITerm]]) : List[(IFormula, IFormula)]

  // Return a canonical object (whose relations are equivalent to the relations of o)
  def canonise(o : LatticeObject) : LatticeObject = o

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice

  //////////////////////////////////////////////////////////////////////////////
 /**
   * 该求不可比元素的函数的输入是两个集合，前一个集合的作用类似top的作用
   * */
  def incomparableSet(Inc : Seq[LatticeObject], Mfc : Seq[LatticeObject]) : Seq[LatticeObject] = { //注意：这里返回值不用迭代器的原因是：如果用迭代器，所得结果在被for循环都访问一遍之后，再循环发现没有元素了
    var newInc = Seq[LatticeObject]();
    for(o <- Inc)
      newInc = newInc ++ incomparable(o, Mfc).toSeq;
    newInc;
  }

  def incomparable(mf : Seq[LatticeObject]) : Iterator[LatticeObject] =
    incomparable(top, mf)
    
  def incomparable(initialTopEl : LatticeObject,
                   mf : Seq[LatticeObject]) : Iterator[LatticeObject] = {
    val incompEls = new ArrayBuffer[LatticeObject]

    def incomparableHelp(topEl : LatticeObject,
                         mf : List[LatticeObject]) : Iterator[LatticeObject] = //更改返回值数据类型为Seq,原因是由于迭代器中的数据访问一遍后就不可再继续访问，再者这里for yield返回值是Vector，可以给Seq
      if (incompEls.exists(latticeOrder.lteq(topEl, _))) {
        Iterator.empty
      } else mf match {
        case List() =>
          Iterator single topEl
        case mfHead :: mfTail =>
          for (x <- incomparableBelow(topEl, mfHead);
               o <- incomparableHelp(x, mfTail)) yield o
      }

    for (o <- incomparableHelp(initialTopEl,
                               mf.sortBy(predNum(_)).toList)) yield {
      incompEls += o
      o
    }
  }

  /**
   * Compute a set S of objects <= topEl that are
   * (i) incomparable to comp, and
   * (ii) S has the property that for every object
   * o <= topEl and !(o <= comp), there is an element u in S such that
   * o <= u.
   * The result of the method is undefined for comp == bottom.
   */
  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject]



  //////////////////////////////////////////////////////////////////////////////

  /**
    * 此类的输入是一个用于判定一个元素是否为可行的函数,该类中包含有三个成员：
    * 1）成员变量cachedFeasible，用于存储缓存的可行元素；
    * 2）成员变量cachedInfeasible，用于存储缓存的不可行元素；
    * 3）成员函数apply,作用是：对于输入的元素，首先获得与此元素o关系等价的标准元素canon，
    *    再判断可行元素集中是否存在某个元素比之小:
    *       如果存在返回true; 【注：此时canon不进行存储】
    *       如果不存在，再判断不可行元素集中是否存在某个元素比之大:
    *           如果存在返回false; 【注：此时canon不进行存储】
    *           如果不存在，判断canon是否可行：
    *               如果可行，添加入可行元素集中并返回true；
    *               如果不可行,添加入不可行元素集中并返回false
    *   结果：cachedFeasible中所存储的元素特征：都是可行的，并且由大到小排列：fe1 > fe2 > fe3 >...
    *         cancedInfeasible中所存储的元素特征：都是不可行的，并且由小到大排列: infe1 < infe2 < infe3 < ...
    *   因此，对于所输入的元素，返回结果为true时，该元素一定是可行的，原因是返回true时，有两种可能性：
    *         其本身可行或者其序关系比别的可行元素序关系大（由于所给抽象格由下往上序关系越来越大，比可行元素大的元素一定是可行的）
    *
    *  综上所述，该类可用于判定元素是否可行，而且还可用于存储部分输入的可行元素和不可行元素
  */
  private class FeasibilityCache(isFeasible: LatticeObject => Boolean) {
    private val cachedFeasible, cachedInfeasible = new ArrayBuffer[LatticeObject]

    def apply(elem : LatticeObject) : Boolean = {
      val canon = canonise(elem) //canonise函数的作用是：求出一个与元素o关系等价的标准元素

      val feasibleIt = cachedFeasible.reverseIterator //获取cachedFeasible的逆序迭代器
      val infeasibleIt = cachedInfeasible.reverseIterator //获取cachedInfeasible的逆序迭代器

      while (feasibleIt.hasNext && infeasibleIt.hasNext) { //对可行元素缓存集与不可行元素缓存集中的元素进行迭代
        if (latticeOrder.lteq(feasibleIt.next, canon))  //如果可行元素缓存集中的元素，比o对应的标准元素序关系小，则返回true
          return true
        if (latticeOrder.lteq(canon, infeasibleIt.next)) //如果o对应的标准元素的序关系比不可行元素缓存集中的元素的序关系比小，则返回false
          return false
      }
     //下面的这两个if是上述while语句中的条件只有一个成立时需考虑的
      if (feasibleIt.hasNext &&
          feasibleIt.exists(e => latticeOrder.lteq(e, canon))) //如果可行元素缓存集中存在一个元素，其序关系比o对应的标准元素序关系小，则返回true
        return true
      if (infeasibleIt.hasNext &&
          infeasibleIt.exists(e => latticeOrder.lteq(canon, e))) //如果o对应的标准元素的序关系比不可行元素缓存集中的元素的序关系比小，则返回false
        return false

      if (isFeasible(canon)) { //如果canon是可行的且序关系要比已有所有元素都小时，则将canon添加到可行缓存集中
        cachedFeasible += canon
        true
      } else {      //如果canon是不可行的且序关系要比已有所有元素都大时，则将canon添加到不可行缓存集中
        cachedInfeasible += canon
        false
      }
    }
  }

  /**
    * 该类的输入是一个timeout值，即搜索抽象格的最长时间，该类包含三个成员：
    * 1）成员变量startTime,用于记录开始搜索抽象格的时间；
    * 2）成员变量printedTimeout，用于记录是否已经打印TIMEOUT,注：当运行Eldarica时的Option选项中没有-log，
    *                            即不需要打印时，也要将此值更为true
    * 3) 成员函数apply, 作用是：如果系统当前时间要超过开始搜索抽象格的时间，则返回true（返回true之前根据-log需要打印timeout）,
    *                           否则返回false。
    *
    *  综上所述，该类主要用于判定抽象格的搜索时间是否超了所输入的timeout值，如果超了，返回true，否则，返回false。
    */
  private class Timeouter(timeout : Long) {
    private val startTime = System.currentTimeMillis  //获取系统开始搜索抽象格的时间
    private var printedTimeout = false //定义布尔变量printedTimeout，顾名思义，是否打印timeout

    def apply = //该函数的意义是：如果系统当前时间要超过开始搜索抽象格的时间，则返回true（返回true之前根据-log需要打印timeout）,否则返回false
      if (System.currentTimeMillis > startTime + timeout) { //该条件表示：如果系统当前时间大于开始搜索抽象格的起始时间+ TO,
                                                          // 注:这个timeout指的是抽象格搜索时间，即执行时-abstractTO:之后的时间
        if (!printedTimeout) { //如果还没有打印TIMEOUT, 并且运行Eldarica时的Option选项中有-log，则打印TIMEOUT,并给布尔变量printedTimeout赋值为true
                                                       //而如果运行Eldarica时的Option选项中没有-log，则直接给布尔变量printedTimeout赋值为true即可
          if (lazabs.GlobalParameters.get.log)
            print(" TIMEOUT")
          printedTimeout = true
        }
        true  //如果已经打印TIMEOUT，则直接返回true即可
      } else { //如果系统当前时间小于开始搜索抽象格的起始时间+TO,则返回false
        false
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  def cheapSearch(isFeasible: LatticeObject => Boolean,
                  timeout : Long = Int.MaxValue) : Seq[LatticeObject] = {
    val objs = search(isFeasible, timeout)
    if(objs.isEmpty) return Seq.empty
    val objsCost = objs.map(o => (o, cost(o)))
    val minEllst = objsCost.unzip._2 : Seq[Int]
    assert(!minEllst.isEmpty)
    val minEl = minEllst.min
    objsCost.filter{ case (v, x) => x == minEl}.unzip._1
  }


  /**
   * Compute minimal feasible elements w.r.t. the given
   * feasibility predicate (which has to be monotonic).
   * Optionally, a timeout in milliseconds can be specified;
   * if a timeout occurs, only minimal feasible elements
   * found up to that point are returned.
   *
   * Beware : starts from top unlike the paper
   */
  def search(isFeasible: LatticeObject => Boolean,
             timeout : Long = Int.MaxValue) : Seq[LatticeObject] = {
    implicit val randGen = new Random (654321)

    val timeIsOut = new Timeouter(timeout)
    val cheapIsFeasible = new FeasibilityCache(isFeasible)

    def minimize(elem : LatticeObject) : LatticeObject = {
      // Get the first feasible element
      val up = pred(elem).find(p => cheapIsFeasible(p)) match {
        case None => return elem
        case Some(f) => f
      }

      assert(up != bottom)
      val m = middle(bottom, up)
      if (cheapIsFeasible(m))
        minimize(m)
      else 
        minimize(up)
    }

    // Calculate minimal feasible for inc 
    def calcMinFeasSet(inc : Iterator[LatticeObject],
                       minFeasEls : Seq[LatticeObject]) : Seq[LatticeObject] = {
      val feasibleInc =
        for (o <- inc; if ({println(o); timeIsOut.apply || cheapIsFeasible(o)})) yield o

      if (feasibleInc.hasNext && !timeIsOut.apply) {
        val feasObj = minimize(feasibleInc.next)
        val newFeasEls = minFeasEls :+ feasObj
        println("new MF object:" + pp(feasObj))
        calcMinFeasSet(incomparable(newFeasEls), newFeasEls) // recurse
      } else {
        minFeasEls
      }
    }

    //val time = System.nanoTime;
    val allFeasibleAbs = 
    if (isFeasible(bottom)) {
      println("bottom abstraction is feasible")
      Seq(bottom)
    } else if (!isFeasible(top)) Seq()
    else{
      val mfe = minimize(top) // get initial min elem from the top
      println("MF object:" + pp(mfe))
      assert(mfe != bottom)
      val inc = incomparable(Seq(mfe)) // Get top level incomparable elements

      calcMinFeasSet(inc, Seq(mfe)) // Call calc minimal feasible
    }

    assert(allFeasibleAbs.filter( x => pred(x).exists( p => isFeasible(p))).isEmpty)
    allFeasibleAbs
  }


  private object TIME_IS_OUT extends Exception

  /**
   * Compute minimal feasible elements w.r.t. the given
   * feasibility predicate (which has to be monotonic).
   * Optionally, a timeout in milliseconds can be specified;
   * if a timeout occurs, only minimal feasible elements
   * found up to that point are returned.
   *
   * Beware : starts from top unlike the paper
   */
  def lSearch(isFeasible: LatticeObject => Boolean,
              //timeout : Long = Int.MaxValue) : Seq[LatticeObject] ={
              timeout : Long = Int.MaxValue) : Seq[LatticeObject] = ap.util.Timer.measure("lSearch"){
    implicit val randGen = new Random (765432)

    val timeIsOut = new Timeouter(timeout)
    val cheapIsFeasible = new FeasibilityCache(isFeasible)

    def cheapIsFeasibleWithTO(elem : LatticeObject) : Boolean =  //表示在给定的timeout时间范围内执行cheapIsFeasible操作，如果超时，则抛出超时异常，并捕获异常。
                                          //函数的作用机理是：在第1个参数所指的timeout checker（实质是一个函数）的背景下，执行第2个参数【进行可行性检测，并捕获此过程中的异常，并且处理异常，即抛出一个TIME_IS_OUT】，
    //                                    //因此二者合起来的含义是：在第1个参数背景下执行可行性检测，如果超时，则第一个参数所指的timeout checker立马会执行timeout.raise(即抛出异常Timeout(None)),而此时第2个参数则
                                          //会即时捕获到此异常，并处理此异常，即抛出一个TIME_IS_OUT.
      Timeout.withChecker { () => //这里的Timeout是import ap.util.Timeout中的内容,但是在网站上的Timeout库中并没有找到withChecker方法，刘琨说可能原因是没有更新库
                                 // 然后选中withChecker,右键goto或者implementation可以去到其定义的地方，明确其含义是：
                                 // 在给定的timeout checker背景下执行代码，注：timeout checker是一个函数，其当timeout发生时，会raise Timeout
        if (timeIsOut.apply)
          Timeout.raise   //raise函数类似于抛出超时异常
      } {
        Timeout.catchTimeout { //catchTimeout实质就是try{}catch{}语句，执行带有异常的代码，捕获异常,并把异常抛出
          cheapIsFeasible(elem)
        } {
          case _ => throw TIME_IS_OUT  //异常抛出
        }
      } //异常处理包含三部分：检测异常，抛出异常，捕获异常，这里withChecker相当于检测异常及抛出异常的部分，catchTimeout相当于捕获异常的部分。


    def minimize(elem : LatticeObject,
                 glBot : LatticeObject,
                 minimalCost : Int) : Either[LatticeObject, LatticeObject] = {

      // newBot
      // new elem, new glbot
//     println("minimize")
//     println(elem)

      if (timeIsOut.apply) throw TIME_IS_OUT

      var learnedBottom = glBot
      var nextFeasible : Option[LatticeObject] = None

      val preds = predCheapestFirst(elem)
                  // predRandom(elem)
      while (!nextFeasible.isDefined && preds.hasNext) {
        val nextPred = preds.next
        if (latticeOrder.lteq(learnedBottom, nextPred)) {
          if (cheapIsFeasibleWithTO(nextPred)) {
            nextFeasible = Some(nextPred)
          } else {
            learnedBottom = join(learnedBottom, getDecrement(elem, nextPred))

            if (cost(learnedBottom) > minimalCost) {
//              println("PRUNING")
              return Right(learnedBottom)
            }
          
            if (cheapIsFeasibleWithTO(learnedBottom))
              return Left(learnedBottom)
          }
        }
      }

      nextFeasible match {
        case None =>
          // elem is an mfe
          if (cost(elem) > minimalCost)
            return Right(elem)
          else
            return Left(elem)
        case Some(nEl) => {
          val m = middle(learnedBottom, nEl)
          // if m is feasible - keep going down
          if (cheapIsFeasibleWithTO(m)){
            minimize(m, learnedBottom, minimalCost)
          } else { // if not feasible go up
            minimize(nEl, learnedBottom, minimalCost)
          }
        }
      }
    }

    // Calculate minimal feasible for inc 
    def calcMinFeasSet(inc : Iterator[LatticeObject], // incomparable elements
                       minFeasEls : Seq[LatticeObject], // minimal feasible set
                       costlyElements : Seq[LatticeObject],
                       topBound : LatticeObject,
                       currentCost : Int
                      ) : Seq[LatticeObject] = {
      if (lazabs.GlobalParameters.get.log)
        print(".")
/*      println("Cheapest MF objects:" + (minFeasEls map (pp _)).mkString(", "))
      println("Costly objects:" + (costlyElements map (pp _)).mkString(", "))
      println("current cost bound: " + currentCost) */

      val feasibleInc =
        for (o <- inc; if (timeIsOut.apply ||
                           (try {
                              cheapIsFeasibleWithTO(o)
                            } catch {
                              case TIME_IS_OUT => true
                            }))) yield o

      if (feasibleInc.hasNext && !timeIsOut.apply) {
        val (newMinFeasEls, newCostlyEls, newTopBound, newCost) = try {
          minimize(feasibleInc.next, bottom, currentCost) match {
            case Left(o) => {
              val oCost = cost(o)
              // found a cheap mfe
              if (oCost < currentCost) {
                if (lazabs.GlobalParameters.get.log) {
                  println
                  println("New cost bound: " + oCost)
                  print("Interpolation abstraction: " + pp(o) + " ")
                }
                (Seq(o), List(), removeExpensivePreds(topBound, oCost), oCost)
              } else {
                assert(oCost == currentCost)
                if (lazabs.GlobalParameters.get.log) {
                  println
                  print("Interpolation abstraction: " + pp(o) + " ")
                }
                (minFeasEls :+ o, costlyElements, topBound, currentCost)
              }
            }
            case Right(o) =>
              // this search direction is too costly
              (minFeasEls, costlyElements :+ o, topBound, currentCost)
          }
        } catch {
           case TIME_IS_OUT =>
             return minFeasEls
        }

        calcMinFeasSet(incomparable(newMinFeasEls ++ newCostlyEls),
                       newMinFeasEls, newCostlyEls, newTopBound, newCost)
      } else {
        minFeasEls
      }
    }

    //val time = System.nanoTime;
    val allFeasibleAbs = 
      if (cheapIsFeasible(bottom)) {
        if (lazabs.GlobalParameters.get.log)
          print("Interpolation abstraction: " + pp(bottom))
        Seq(bottom)
      } else if (!cheapIsFeasible(top)) {
        if (lazabs.GlobalParameters.get.log)
          print("Top interpolation abstraction is not feasible")
        Seq()
      } else {
        val Left(mfe) = try {
          minimize(top, bottom, cost(top))
        } catch {
           case TIME_IS_OUT =>
             return Seq()
        }

        val minCost = cost(mfe)
        val topBound = removeExpensivePreds(top, minCost)

        if (lazabs.GlobalParameters.get.log) {
          println("Cost bound: " + minCost)
          print("Interpolation abstraction: " + pp(mfe) + " ")
        }
        //assert(mfe != bottom && newBot > mfe)
      
        val inc = incomparable(topBound, Seq(mfe))
        calcMinFeasSet(inc, Seq(mfe), Seq(), topBound, minCost)
      }

//    assert(allFeasibleAbs.filter( x => pred(x).exists( p => isFeasible(p))).isEmpty)
    if (lazabs.GlobalParameters.get.log)
      println
    allFeasibleAbs
  }

 /**
   *
   * */
  def fSearch(isFeasible: LatticeObject => Boolean,  //输入一个函数isFeasible和一个Long型的变量timeout，前者用于判定一个抽象格元素是否可行，后者用于判定是否超时
               timeout : Long = Int.MaxValue) : Seq[LatticeObject] = ap.util.Timer.measure("fSearch") {

    val cheapIsFeasible = new FeasibilityCache(isFeasible)
    val timeIsOut = new Timeouter(timeout) //RQ4:timeout问题处理

    def cheapIsFeasibleWithTO(elem: LatticeObject): Boolean =
      Timeout.withChecker { () =>
        if (timeIsOut.apply)
          Timeout.raise
      } {
        Timeout.catchTimeout {
          cheapIsFeasible(elem)
        } {
          case _ => throw TIME_IS_OUT
        }
      }


    def succWithIncSetLimit(incSet:Seq[LatticeObject], elem: LatticeObject, existSuccSet: Seq[LatticeObject]):Seq[LatticeObject] = {
      var newsuccSet = existSuccSet;
      def succWithIncSetLimitNoSuccSet(incSet_1 :Seq[LatticeObject],elem_1:LatticeObject):Seq[LatticeObject] = {
        for (incElem <- incSet_1) {
          var succLimitSet = incomparable(incElem, newsuccSet).filter(o => (latticeOrder.lteq(elem_1, o) && cheapIsFeasibleWithTO(o))).toSeq;

          if (!succLimitSet.isEmpty && succLimitSet.size == 1)
            newsuccSet ++= succWithLimit(elem_1, succLimitSet.head);
          else if (!succLimitSet.isEmpty && succLimitSet.size != 1 )
            succWithIncSetLimitNoSuccSet(succLimitSet, elem_1)
        }
        return newsuccSet;
      }
      succWithIncSetLimitNoSuccSet(incSet,elem);
    }

    var WaitList = Seq[LatticeObject](bottom) //为方便定义g，将WaitList定义为一个Map，定义一个空的映射，用于存储抽象格元素及其对应的g值
    // WaitList = Map(bottom -> 0); //这里是对WaitList进行初始化【注：以前操作：Seq默认是不可变的,这里将数据类型换为ArrayBuffer是为了方便处理】
    var CostlyList = Seq[LatticeObject](); //格式正确，但是需引入import scala.collection.mutable.ArrayBuffer
    var FrontierList = Seq[LatticeObject]();
    var minCost = cost(top); //无穷大表示不清楚，使之取值为抽象格中最大的cost吧，由于cost函数定义时，是由格的下方到上方，随序关系增大，cost函数递增的，所以top序关系最大

    //def g(elem : LatticeObject): Int //如何声明一个函数    —— 解决：令WaitList为一个映射来处理
    //def g(bottom) = 0 //函数如何赋值；
    var IncList = Seq(top);
    //var succLimit = IncList;
    var CostlyWaitList = Seq[LatticeObject]() //由ArrayBuffer转为Seq，原因是为了获取WaitList中的键集
    if (cheapIsFeasible(bottom)){ // RQ1. 判断一个元素是否可行，用isFeasible函数好，还是用cheapIsFeasible函数好？  ---解决方案：除top和bottom元素用cheapIsFeasible之外，其它用cheapIsFeasibleWithTO
      if (lazabs.GlobalParameters.get.log)
        print("Interpolation abstraction: " + pp(bottom))
      //FrontierList = FrontierList :+ bottom; // ArrayBuffer中添加元素可以用 +=和 :+
      Seq(bottom);
    }else if (!cheapIsFeasible(top)) {
      if (lazabs.GlobalParameters.get.log)
        print("Top interpolation abstraction is not feasible")
      //FrontierList = List[LatticeObject]();
      Seq();
    }else{
      try{
        while (!WaitList.isEmpty && !IncList.isEmpty && !timeIsOut.apply ) { //如果要扩展某个元素时超时，则直接返回目前找到的Frontierlist
          var minElem = WaitList.minBy(p => cost(p))
          //WaitList -=  minElem; //从映射中删除元素时，只需删除键就可以;为了定义g方便，而在一次while循环结束时才删除minElem
          var IncListCache = IncList; //新添加的，用以缓存每次扩展一个节点前的IncList
          //var incElem = IncList.minBy(p => cost(p));
          if (timeIsOut.apply) throw TIME_IS_OUT;
         /* ???var incElem = IncListCache.find(o => latticeOrder.lteq(minElem,o))
          ???if (incElem match case Some(m))

          ???IncList = (IncList.toBuffer - .toSeq;*/

          // ??? for (incElem <- IncListCache.find)
          /*var incNum = IncList.size;
          var incCounter = 0;
          for (o <- IncListCache)
            { incCounter = incCounter +1;
              println;
             println("incomparable element" + incCounter + pp(o));}
          println;
          println("Incomparable element print end")*/

          //var incElem = IncListCache.filter(o => latticeOrder.lteq(minElem,o)).head
          //122620var succSet = Seq[LatticeObject]()
          //122620 for (incElem <-IncListCache) {

          //122620  var succSetCache = incomparableSet(Seq(incElem), succSet).filter(o => (latticeOrder.lteq(minElem, o) && cheapIsFeasibleWithTO(o) ) ).toSeq;
          //122620   for( o <- succSet )
          //122620    {
          //122620      println;
          //122620       println("old succSet member:" ++ pp(o))
          //122620    }
          //122620  println("old succSet println end");
          //122620  println

          //122620   for( o <- succSetCache )
          //122620  {
          //122620   println;
          //122620    println("new succSetCache member:" ++ pp(o))
          //122620 }
          //122620 println("old succSetCache println end");
          //122620  println


            // var succSetCache = succSet;
           //122620 for ( succLimit <- succSetCache;
            //122620 succElem <- succWithLimit(minElem, succLimit)) { //RQ2. 以不可比元素为界，求后继元素的思想？
              // ----解决方案：在AbsLattice中进行了定义，并在其三大子类BitSetLattice, ProductLattice和ExtendingLattice中进行了实现。
          //122620   println("Incomparable" + pp(incElem));
          //122620    println;
          //122620    println("Successor" + pp(succElem));
           var succSetofminElem = succWithIncSetLimit(IncListCache, minElem,Seq())
          for (o <- succSetofminElem)
            {println;
            println("Succ member:" + pp(o))
            }
           println;
           println("SUCC Print END");


           for (succElem <- succSetofminElem) {
              if (timeIsOut.apply) throw TIME_IS_OUT;
              if ( !IncListCache.contains(succElem)  || cheapIsFeasibleWithTO(succElem)) { //这个||条件替换了一个分支
                //g(succElem) = g(minElem) + 1;
                if (cost(succElem) < minCost) {
                  if (cheapIsFeasibleWithTO(succElem)) {
                    minCost = cost(succElem);
                    CostlyList = FrontierList;
                    FrontierList = Seq(succElem);
                    IncList = incomparable(FrontierList ++ CostlyList).filter(e => cheapIsFeasibleWithTO(e)).toSet.toSeq; //incomparable函数的
                    if (lazabs.GlobalParameters.get.log) {
                      println
                      println("New Cost bound: " + minCost)
                      print("Interpolation abstraction: " + pp(succElem) + " ")
                      println
                      for (o <- IncList) {
                        println(pp(o));
                        println;
                      }
                      println("new incomparable set(new cost interpolation abstraction) println end")
                    }
                  }
                  else {
                    WaitList = WaitList :+ succElem; //集合中加元素用:+（元素添加在集合后面）或者+:（元素添加在集合前面），下一行没有去定义f
                  }
                }
                else if (cost(succElem) == minCost) { //scala中有else if
                  if (cheapIsFeasibleWithTO(succElem)) {
                    FrontierList ++= Seq(succElem);
                    IncList = incomparable(FrontierList ++ CostlyList).filter(e => cheapIsFeasibleWithTO(e)).toSet.toSeq; //incomparable函数的定义
                    if (lazabs.GlobalParameters.get.log) {
                      println
                      print("Interpolation abstraction: " + pp(succElem) + " ")
                      for (o <- IncList) {
                        println(pp(o));
                        println;
                      }
                      println("new incomparable set(old cost feasible interpolation abstraction) println end")
                    }
                  }
                  else {
                    CostlyList = CostlyList :+ succElem; //集合中加元素用:+（元素添加在集合后面）或者+:（元素添加在集合前面）
                    IncList = incomparable(FrontierList ++ CostlyList).filter(e => cheapIsFeasibleWithTO(e)).toSet.toSeq;
                    for (o <- IncList) {
                      println(pp(o));
                      println;
                    }
                    println("new incomparable set(old cost infeasible interpolation abstraction) println end")
                  }
                }
                else {
                  CostlyList = CostlyList :+ succElem; //集合中加元素用:+（元素添加在集合后面）或者+:（元素添加在集合前面）
                  IncList = incomparable(FrontierList ++ CostlyList).filter(e => cheapIsFeasibleWithTO(e)).toSet.toSeq
                  for (o <- IncList) {
                    println(pp(o));
                    println;
                  }
                  println("new incomparable set(costly interpolation abstraction) println end")

                }
              } //endif if(succElem != incElem || isFeasible(succElem))//endfor for(succElem <- incomparSucc(minElem, incElem))
              //1226succSet = succSet :+ succElem;
              //1226println("new succSet member" + pp(succElem))
               //endfor for(incElem <- IncList)

          }

          if (lazabs.GlobalParameters.get.log)
            print(".")
          if (!timeIsOut.apply)
          {
            WaitList = (WaitList.toBuffer - minElem).toSeq;
            CostlyWaitList = WaitList.filter(p => (cost(p) >= minCost)).toSeq;
            CostlyList ++= CostlyWaitList;
            IncList = incomparable(FrontierList ++ CostlyList).filter(e => cheapIsFeasibleWithTO(e)).toSet.toSeq; //RQ3. 不可比函数如何写？  ——解决方案：重新定义
            //succLimit = IncList.filterNot(o => latticeOrder.lteq(minElem,o))
            WaitList = WaitList.toBuffer --IncList; //集合之间相减可以用--=,这里WaitList是一个映射，去掉元素集时，只需去掉key集合即可。
            WaitList = WaitList.toBuffer -- CostlyWaitList;
            for (o <- IncList) {
              println("incomparable elements:" + pp(o));
              println;
            }
            println("the newest new incomparable set println end")

           //1226 for (o <- WaitList) {
            //1226   println("waitlist member" + pp(o));
            //1226    println;
            //1226  }
            //1226  println("new waitLIst member  println end")
            // IncList = IncList.filter(e => (cheapIsFeasibleWithTO(e))); //表示从不可比列表中找可行元素，一旦发现超时异常，则直接返回所找到的最小可行元素集即可
          } else  throw TIME_IS_OUT;
        }
        if (lazabs.GlobalParameters.get.log)
          println
        FrontierList;
      } catch {
        case TIME_IS_OUT => return FrontierList
      };
    }; // endwhile while(!WaitList.isEmpty && !IncList.isEmpty)
    ////ArrayBuffer是mutable.Seq的子类,因此，没有必要加toSeq
  } //endfunction fSearch

  def bidirSearch(isFeasible: LatticeObject => Boolean,  //输入一个函数isFeasible和一个Long型的变量timeout，前者用于判定一个抽象格元素是否可行，后者用于判定是否超时
              timeout : Long = Int.MaxValue) : Seq[LatticeObject] = ap.util.Timer.measure("bidirSearch") {

    implicit val randGen = new Random (765432) //调用middle函数时使用
    val cheapIsFeasible = new FeasibilityCache(isFeasible)
    val timeIsOut = new Timeouter(timeout) //RQ4:timeout问题处理

    def cheapIsFeasibleWithTO(elem: LatticeObject): Boolean =
      Timeout.withChecker { () =>
        if (timeIsOut.apply)
          Timeout.raise
      } {
        Timeout.catchTimeout {
          cheapIsFeasible(elem)
        } {
          case _ => throw TIME_IS_OUT
        }
      }

    def minimize(elem: LatticeObject,
                 glBot: LatticeObject,
                 minimalCost: Int): Either[LatticeObject, LatticeObject] = {

      // newBot
      // new elem, new glbot
      //     println("minimize")
      //     println(elem)

      if (timeIsOut.apply) throw TIME_IS_OUT

      var learnedBottom = glBot
      var nextFeasible: Option[LatticeObject] = None

      val preds = predCheapestFirst(elem)
      // predRandom(elem)
      while (!nextFeasible.isDefined && preds.hasNext) {
        val nextPred = preds.next
        if (latticeOrder.lteq(learnedBottom, nextPred)) {
          if (cheapIsFeasibleWithTO(nextPred)) {
            nextFeasible = Some(nextPred)
          } else {
            learnedBottom = join(learnedBottom, getDecrement(elem, nextPred))

            if (cost(learnedBottom) > minimalCost) {
              //              println("PRUNING")
              return Right(learnedBottom)
            }

            if (cheapIsFeasibleWithTO(learnedBottom))
              return Left(learnedBottom)
          }
        }
      }

      nextFeasible match {
        case None =>
          // elem is an mfe
          if (cost(elem) > minimalCost)
            return Right(elem)
          else
            return Left(elem)
        case Some(nEl) => {
          val m = middle(learnedBottom, nEl)
          if (cheapIsFeasibleWithTO(m)) {
            minimize(m, learnedBottom, minimalCost)
          } else { // if not feasible go up
            minimize(nEl, learnedBottom, minimalCost)
          }
        }
      }
    }


    def succWithIncSetLimit(incSet: Seq[LatticeObject], elem: LatticeObject, existSuccSet: Seq[LatticeObject]): Seq[LatticeObject] = {
      var newsuccSet = existSuccSet;
      def succWithIncSetLimitNoSuccSet(incSet_1: Seq[LatticeObject], elem_1: LatticeObject): Seq[LatticeObject] = {
        for (incElem <- incSet_1) {
          var succLimitSet = incomparable(incElem, newsuccSet).filter(o => (latticeOrder.lteq(elem_1, o) && cheapIsFeasibleWithTO(o))).toSeq;

          if (!succLimitSet.isEmpty && succLimitSet.size == 1)
            newsuccSet ++= succWithLimit(elem_1, succLimitSet.head);
          else if (!succLimitSet.isEmpty && succLimitSet.size != 1)
            succWithIncSetLimitNoSuccSet(succLimitSet, elem_1)
        }
        return newsuccSet;
      }

      succWithIncSetLimitNoSuccSet(incSet, elem);
    }

    var WaitList = Seq[LatticeObject](bottom)
    var CostlyList = Seq[LatticeObject]();
    var FrontierList = Seq[LatticeObject]();
    var minCost = cost(top); //无穷大表示不清楚，使之取值为抽象格中最大的cost吧，由于cost函数定义时，是由格的下方到上方，随序关系增大，cost函数递增的，所以top序关系最大


    var IncList = Seq(top);
    //var CostlyWaitList = Seq[LatticeObject]() //由ArrayBuffer转为Seq，原因是为了获取WaitList中的键集


    //minElem及其后继集、可行后继集与不可行后继集
    var minElem = bottom;
    var lastMinElem = bottom;
    var lastLayerInfeasibleSuccSet = Seq[LatticeObject]();
    var succSet = Seq[LatticeObject]()
    var feasibleSuccSet = Seq[LatticeObject]();
    var infeasibleSuccSet = Seq[LatticeObject]();

    var learnedBottom = bottom;

    if (cheapIsFeasible(bottom)) { // RQ1. 判断一个元素是否可行，用isFeasible函数好，还是用cheapIsFeasible函数好？  ---解决方案：除top和bottom元素用cheapIsFeasible之外，其它用cheapIsFeasibleWithTO
      if (lazabs.GlobalParameters.get.log)
        print("Interpolation abstraction: " + pp(bottom))
      //FrontierList = FrontierList :+ bottom; // ArrayBuffer中添加元素可以用 +=和 :+
      Seq(bottom);
    } else if (!cheapIsFeasible(top)) {
      if (lazabs.GlobalParameters.get.log)
        print("Top interpolation abstraction is not feasible")
      //FrontierList = List[LatticeObject]();
      Seq();
    } else {
      try {
        while (!WaitList.isEmpty && !IncList.isEmpty && !timeIsOut.apply) { //如果要扩展某个元素时超时，则直接返回目前找到的Frontierlist

          //WaitList = WaitList.toBuffer - minElem;

          //var oldSuccSet = succSet;
          succSet = succWithIncSetLimit(IncList, minElem, Seq());  //这里第3个参数的输入没有必要是oldSuccSet，原因是：即使新的minElem与旧的是同层的，则由于旧的是可行的，则与之可比的元素一定会删除掉【不可比集得到了更新】，因此，不必担心计算新的minElem后继时会遇到与旧的minElem相同的。
          feasibleSuccSet = succSet.filter(p => cheapIsFeasibleWithTO(p));
          infeasibleSuccSet = succSet.toBuffer -- feasibleSuccSet.toBuffer;

          if (timeIsOut.apply) throw TIME_IS_OUT;

          //以下用于调试使用；
         /* for (o <- feasibleSuccSet) {
            println;
            println("Feasible Succ member:" + pp(o))
          }
          println;
          println("Feasible SUCC Print END");

           for (o <- infeasibleSuccSet) {
             println;
             println("InFeasible Succ member:" + pp(o))
           }
           println;
           println("InFeasible SUCC Print END");*/

          //用于调试使用；

          //if(! feasibleSuccSet.isEmpty)
          for (feasibleSuccElem <- feasibleSuccSet) {
            if (timeIsOut.apply) throw TIME_IS_OUT;
            if (!predCheapestFirst(feasibleSuccElem).exists(o => cheapIsFeasible(o))) {
              if (cost(feasibleSuccElem) < minCost) {
                if (lazabs.GlobalParameters.get.log) {
                  println
                  println("New cost bound: " + cost(feasibleSuccElem))
                  print("Interpolation abstraction: " + pp(feasibleSuccElem) + " ")
                }
                minCost = cost(feasibleSuccElem);
                CostlyList = FrontierList;
                FrontierList = Seq(feasibleSuccElem);
              }
              else if (cost(feasibleSuccElem) == minCost) {
                if (lazabs.GlobalParameters.get.log) {
                  println
                  print("Interpolation abstraction: " + pp(feasibleSuccElem) + " ")
                }
                FrontierList = FrontierList :+ feasibleSuccElem;
              }
              else
                CostlyList = CostlyList :+ feasibleSuccElem;
            }
            else {
              learnedBottom = join(learnedBottom, getDecrement(feasibleSuccElem, minElem));
              //var feasiblePredElem = predCheapestFirst(feasibleSuccElem).find(o =>cheapIsFeasibleWithTO(o)).get;
              var result = minimize(feasibleSuccElem, learnedBottom, minCost);
              result match {
                case Left(m) => {
                  if (cost(m) < minCost) {
                    if (lazabs.GlobalParameters.get.log) {
                      println
                      println("New cost bound: " + cost(m))
                      print("Interpolation abstraction: " + pp(m) + " ")
                    }
                    minCost = cost(m);
                    CostlyList = FrontierList;
                    FrontierList = Seq(m);
                  }
                  else {
                    if (lazabs.GlobalParameters.get.log) {
                      println
                      print("Interpolation abstraction: " + pp(m) + " ")
                    }
                    FrontierList = FrontierList :+ m;
                  }
                }
                case Right(c) =>
                  CostlyList = CostlyList :+ c;
              }
            }
          } //end for 循环,表示所有可行元全部考虑完

          //var costlyInfeasibleSuccElem = infeasibleSuccSet.filter(o => cost(o) >= minCost);
          //infeasibleSuccSet = (infeasibleSuccSet.toBuffer -- costlyInfeasibleSuccElem).toSet.toSeq;
          //if(!feasibleSuccSet.isEmpty) {
            infeasibleSuccSet = infeasibleSuccSet.filter(o => cost(o) < minCost).toSet.toSeq
            //CostlyList ++= costlyInfeasibleSuccElem.filter(p => !CostlyList.exists(q => latticeOrder.lteq(q,p))); //去掉此行目的是为了减小infeasible集合的计算负担;但是所包含内容确实是costly元素

            //var costlyWaitListElem = WaitList.filter(o => cost(o) >= minCost);
            //WaitList = WaitList.toBuffer -- costlyWaitListElem;
            WaitList = (WaitList.filter(o => cost(o) < minCost)++ infeasibleSuccSet).toSet.toSeq ; //Line1016有添加
            //CostlyList = (CostlyList ++ (costlyWaitListElem ++ costlyInfeasibleSuccElem).filter(p => !CostlyList.exists(q => latticeOrder.lteq(q,p)))).toSet.toSeq;

            IncList = incomparable(FrontierList ++ CostlyList).toSet.toSeq.filter(o => cheapIsFeasibleWithTO(o));





          if (lazabs.GlobalParameters.get.log)
            print(".")

          if (!timeIsOut.apply) {

            //IncList = incomparable(FrontierList ++ CostlyList).toSet.toSeq.filter(o => cheapIsFeasibleWithTO(o)); //去除IncList中的相同元素；
            //IncList = incomparable(FrontierList ++ CostlyList).toSet.toSeq.filter(o => cheapIsFeasibleWithTO(o));
            //以下代码用于调试使用
            /*for (o <- IncList) {
              println("incomparable elements:" + pp(o));
              println;
            }
            println("Incomparable elements Print END")*/
            //以上代码用于调试使用
            //var sortedInfeasibleSuccSet = infeasibleSuccSet.sortBy(o => cost(o));

            //if (!infeasibleSuccSet.isEmpty) {
            if(!infeasibleSuccSet.filter(p  => (IncList.exists(q => latticeOrder.lteq(p, q)) && cost(p) < minCost)).isEmpty){
              //minElem = infeasibleSuccSet.filter(p => IncList.exists(q => latticeOrder.lteq(p, q))).minBy(o => cost(o));
              lastMinElem = minElem;  //只有在后继中有元素可扩展的时候才改变lastMinElem;
              lastLayerInfeasibleSuccSet = infeasibleSuccSet;
              minElem = infeasibleSuccSet.filter(p  => (IncList.exists(q => latticeOrder.lteq(p, q)) && cost(p) < minCost)).minBy(o => cost(o));
              infeasibleSuccSet = infeasibleSuccSet.toBuffer - minElem;
              WaitList = WaitList.toBuffer - minElem;
             /* println
              println("minElem is:" + pp(minElem));
              println;*/
            }else{
              IncList = incomparable(FrontierList ++ CostlyList :+ minElem).toSet.toSeq.filter(o => cheapIsFeasibleWithTO(o))
              if(lastLayerInfeasibleSuccSet.sortBy(o => cost(o)).find(p => IncList.exists(q => latticeOrder.lteq(p, q)) && cost(p) < minCost).isDefined) {
                 minElem = lastLayerInfeasibleSuccSet.sortBy(o => cost(o)).find(p => IncList.exists(q => latticeOrder.lteq(p, q)) && cost(p) < minCost).get
                 lastLayerInfeasibleSuccSet = lastLayerInfeasibleSuccSet.toBuffer - minElem;
                WaitList = WaitList.toBuffer - minElem;
              }else{
                IncList = incomparable(FrontierList ++ CostlyList :+ lastMinElem).toSet.toSeq.filter(o => cheapIsFeasibleWithTO(o))
                //else if(!WaitList.filter(p => IncList.exists(q => latticeOrder.lteq(p, q))).isEmpty) {
                if(WaitList.sortBy(o => cost(o)).find(p  => IncList.exists(q => latticeOrder.lteq(p, q))).isDefined) {
                  //minElem = WaitList.filter(p => IncList.exists(q => latticeOrder.lteq(p, q))).minBy(o => cost(o));
                  minElem = WaitList.sortBy(o => cost(o)).find(p  => IncList.exists(q => latticeOrder.lteq(p,q))).get ;
                  WaitList = WaitList.toBuffer - minElem;
                  //WaitList = WaitList.toBuffer - minElem; //2019/12/30修改，原因是Line877行有删减
                  /*println
                  println("minElem is:" + pp(minElem));
                  println;*/
                } else {
                  if (!FrontierList.isEmpty)
                    return FrontierList;
                  else
                    return IncList;
                }
              }
            }

           // WaitList = ((WaitList ++ infeasibleSuccSet).toBuffer -- IncList).toSet.toSeq; //去除WaitList中所包含的IncList中的元素，及其相同元素；
           // WaitList = (WaitList ++ infeasibleSuccSet).toSet.toSeq;   //2019/12/31修改：IncList都是可行元素
            //以下代码用于调试使用
            /*for (o <- WaitList) {
              println("WaitList elements:" + pp(o));
              println;
            }
            println("WaitList elements Print END")*/
            //以上代码用于调试使用

          } else throw TIME_IS_OUT;
        }
        if (lazabs.GlobalParameters.get.log)
          println
        if(!FrontierList.isEmpty)
          return FrontierList;
        else
          return IncList;
      } catch {
        case TIME_IS_OUT => return FrontierList
      };
    };
  }


  //////////////////////////////////////////////////////////////////////////////

  /**
   * Do a complete encoding of the the composed relation
   * R_A[xa, x] \circ R_B[x, xb] with the help of Boolean flags.
   * Returned are the flags, as well as a translator from flag
   * valuations to lattice elements.
   */
  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]],
                         p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject)

}

////////////////////////////////////////////////////////////////////////////////

// Product lattice, inductive class

object ProductLattice {
  def apply[A <: AbsLattice, B <: AbsLattice](a : A, b : B) =
    new ProductLattice(a, b, false)
  def apply[A <: AbsLattice, B <: AbsLattice](a : A, b : B,
                                              conjunction : Boolean) =
    new ProductLattice(a, b, conjunction)
}

class ProductLattice[A <: AbsLattice, B <: AbsLattice] private (val a : A, val b : B,
                                                                conjunction : Boolean)
      extends AbsLattice {
  type LatticeObject = (a.LatticeObject, b.LatticeObject)

  override def toString =
    "" + a + (if (conjunction) " & " else " * ") + b

  def pp(o : LatticeObject) =
    a.pp(o._1) + (if (conjunction) " & " else ", ") + b.pp(o._2)

  val top = (a.top, b.top)
  val bottom = (a.bottom, b.bottom)

  // normal partial order
  val latticeOrder = new PartialOrdering[LatticeObject] {
    def tryCompare(x: LatticeObject, y: LatticeObject) =
      for (c1 <- a.latticeOrder.tryCompare(x._1, y._1);
           c2 <- b.latticeOrder.tryCompare(x._2, y._2);
           if (c1 * c2 != -1))
      yield (c1, c2) match {
        case (1, _) | (_, 1) => 1
        case (-1, _) | (_, -1) => -1
        case _ => 0
      }
 
    def lteq(x: LatticeObject, 
             y: LatticeObject) =
      a.latticeOrder.lteq(x._1, y._1) && b.latticeOrder.lteq(x._2, y._2)
  }

  val arity =
    if (conjunction) {
      assert(a.arity == b.arity)
      a.arity
    } else {
      a.arity + b.arity
    }

  def meet(x: LatticeObject, y: LatticeObject): LatticeObject =
      (a.meet(x._1, y._1), b.meet(x._2, y._2))

  def join(x: LatticeObject, y: LatticeObject): LatticeObject =
      (a.join(x._1, y._1), b.join(x._2, y._2))

  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject =
    (a.removeExpensivePreds(obj._1, bound), b.removeExpensivePreds(obj._2, bound))

  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject =
    if (feasible._1 == infeasible._1)
      (a.bottom, b.getDecrement(feasible._2, infeasible._2))
    else if (feasible._2 == infeasible._2)
      (a.getDecrement(feasible._1, infeasible._1), b.bottom)
    else
      bottom

  // normal order
  def succ(x: LatticeObject): Iterator[LatticeObject] =
    (for (as <- a.succ(x._1)) yield (as, x._2)) ++ (
     for (bs <- b.succ(x._2)) yield (x._1, bs))

  def pred(x: LatticeObject): Iterator[LatticeObject] =
    (for (ap <- a.pred(x._1)) yield (ap, x._2)) ++ (
     for (bp <- b.pred(x._2)) yield (x._1, bp))

  def succWithLimit(obj:LatticeObject, topEl:LatticeObject) : Iterator[LatticeObject] =
    ( for (as <- a.succWithLimit(obj._1, topEl._1))  yield (as, obj._2)) ++ (
      for (bs <- b.succWithLimit(obj._2, topEl._2)) yield(obj._1, bs))

  private def mergeCheapestFirst(aBase : a.LatticeObject,
                                 bBase : b.LatticeObject,
                                 aIt : Iterator[a.LatticeObject],
                                 bIt : Iterator[b.LatticeObject]) =
    new Iterator[LatticeObject] {
      val aPeek = PeekIterator(aIt)
      val bPeek = PeekIterator(bIt)

      val aCost = a.cost(aBase)
      val bCost = b.cost(bBase)

      def hasNext = aPeek.hasNext || bPeek.hasNext

      def next =
        if (aPeek.hasNext) {
          if (bPeek.hasNext &&
              a.cost(aPeek.peekNext) + bCost > aCost + b.cost(bPeek.peekNext)) {
            (aBase, bPeek.next)
          } else {
            (aPeek.next, bBase)
          }
        } else {
          (aBase, bPeek.next)
        }
    }

  def predCheapestFirst(x: LatticeObject) =
    mergeCheapestFirst(x._1, x._2,
                       a.predCheapestFirst(x._1),
                       b.predCheapestFirst(x._2))

  def predRandom(x: LatticeObject)
                (implicit randGen : Random) = new Iterator[LatticeObject] {
    val aIt = a.predRandom(x._1)
    val bIt = b.predRandom(x._2)

    def hasNext = aIt.hasNext || bIt.hasNext

    def next =
      if (!aIt.hasNext)
        (x._1, bIt.next)
      else if (!bIt.hasNext)
        (aIt.next, x._2)
      else if (randGen.nextBoolean)
        (aIt.next, x._2)
      else
        (x._1, bIt.next)
  }

  def predNum(x: LatticeObject): Int = a.predNum(x._1) + b.predNum(x._2)

  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) : LatticeObject = {
    val fmid = a.middle(lower._1, upper._1)
    val smid = b.middle(lower._2, upper._2)
    (fmid, smid)
  }

  def cost(obj : LatticeObject) : Int =
    a.cost(obj._1) + b.cost(obj._2)

  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] =
    if (latticeOrder.lteq(topEl, comp))
      Iterator.empty
    else if (latticeOrder.lteq(comp, topEl))
      mergeCheapestFirst(topEl._1, topEl._2,
                         a.incomparableBelow(topEl._1, comp._1),
                         b.incomparableBelow(topEl._2, comp._2))
//      (for (x <- a.incomparableBelow(topEl._1, comp._1)) yield (x, topEl._2)) ++
//      (for (x <- b.incomparableBelow(topEl._2, comp._2)) yield (topEl._1, x))
    else
      Iterator single topEl

  def asRelation(obj : LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] =
    if (conjunction)
      for ((f, g) <- a.asRelation(obj._1, xa, xb) zip b.asRelation(obj._2, xa, xb))
      yield (f & g)
    else
      a.asRelation(obj._1, xa.take(a.arity), xb.take(a.arity)) ++ 
      b.asRelation(obj._2, xa.drop(a.arity), xb.drop(a.arity))

  def asRelation(obj : LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
    if (conjunction)
      for (((f1, f2), (g1, g2)) <-
             a.asRelation(obj._1, xa, x, xb) zip b.asRelation(obj._2, xa, x, xb))
      yield (f1 & g1, f2 & g2)
    else
      a.asRelation(obj._1, xa.take(a.arity), x.take(a.arity), xb.take(a.arity)) ++ 
      b.asRelation(obj._2, xa.drop(a.arity), x.drop(a.arity), xb.drop(a.arity))

  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]], p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject) =
    if (conjunction) {
      val (aFlags, aFun) = a.genBooleanEncoding(xa, xb, p)
      val (bFlags, bFun) = b.genBooleanEncoding(xa, xb, p)
      (aFlags ++ bFlags,
       flags => (aFun(flags take aFlags.size), bFun(flags drop aFlags.size)))
    } else {
      val (aFlags, aFun) = a.genBooleanEncoding(xa.take(a.arity), xb.take(a.arity), p)
      val (bFlags, bFun) = b.genBooleanEncoding(xa.drop(a.arity), xb.drop(a.arity), p)
      (aFlags ++ bFlags,
       flags => (aFun(flags take aFlags.size), bFun(flags drop aFlags.size)))
    }

  override def canonise(o : LatticeObject) : LatticeObject =
    (a.canonise(o._1), b.canonise(o._2))

  // The reduced lattice corresponding to this lattice
  lazy val reducedLattice : AbsLattice =
    new ProductLattice(a.reducedLattice, b.reducedLattice, conjunction)
}

////////////////////////////////////////////////////////////////////////////////

abstract class BitSetLattice(width : Int, name : String) extends AbsLattice {

  val arity : Int

  protected def pp(bit : Int) : String

  protected def bitCost(bit : Int) : Int

  //////////////////////////////////////////////////////////////////////////////

  type LatticeObject = BitSet

  def pp(o : LatticeObject) =
    (name match { case "" => ""; case n => n + ": " }) +
    "<" + (for (i <- o) yield pp(i)).mkString(", ") + ">"

  val latticeOrder = new PartialOrdering[LatticeObject] {
    def tryCompare(x: LatticeObject, y: LatticeObject) =
      (x subsetOf y, y subsetOf x) match {
        case (true, true)  => Some(0)
        case (true, false) => Some(-1)
        case (false, true) => Some(1)
        case _ => None
      }

    def lteq(x: LatticeObject, y: LatticeObject) = x subsetOf y
  }

  val top = BitSet((0 until width): _*)
  val bottom = BitSet.empty

  def meet(x : LatticeObject , y: LatticeObject) : LatticeObject = x intersect y
  def join(x: LatticeObject, y: LatticeObject) : LatticeObject  = x union y

  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject =
    obj filter (i => bitCost(i) <= bound)

  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject = {
    val step = feasible -- infeasible
    if (step.size == 1) step else bottom
  }

  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) : LatticeObject = {
    val nelem = for (x <- upper;
                     if ( (lower contains x) || randGen.nextInt(100) < 80)) yield x
    assert(latticeOrder.lteq(bottom, nelem))
    nelem
  }

  def cost(obj : LatticeObject) : Int =
    (for (i <- obj.iterator) yield bitCost(i)).sum

  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] =
    if (latticeOrder.lteq(topEl, comp))
      Iterator.empty
    else if (latticeOrder.lteq(comp, topEl))
      for (t <- comp.iterator) yield (topEl - t)
    else
      Iterator single topEl

  def succ (obj: LatticeObject) : Iterator[LatticeObject] =
    for (t <- top.iterator; if (!(obj contains t))) yield (obj + t) //前趋和后继的计算思路与自己所想象的是一样的，前趋元素少，后继越来越多

  def pred(obj: LatticeObject) : Iterator[LatticeObject] =
    for (t <- top.iterator; if (obj contains t)) yield (obj - t)

  def succWithLimit(obj:LatticeObject, topEl:LatticeObject) : Iterator[LatticeObject] =
    for (t <- topEl.iterator;  if (!(obj contains t))) yield (obj + t)


  lazy val objseqCostlyFirst =
    (0 until width).toArray sortBy { i => -bitCost(i) }

  def predCheapestFirst(obj: LatticeObject) : Iterator[LatticeObject ] =
    for (t <- objseqCostlyFirst.iterator; if (obj contains t)) yield (obj - t)

  def predRandom(x: LatticeObject)
                (implicit randGen : Random) = new Iterator[LatticeObject] {
    private val remaining = new MBitSet
    remaining ++= x

    def hasNext = !remaining.isEmpty

    def next = {
      val selected =
        if (remaining.size > 1) {
          val it = remaining.iterator
          for (_ <- 0 until randGen.nextInt(remaining.size))
            it.next
          it.next
        } else {
          remaining.head
        }
      remaining -= selected
      x - selected
    }
  }

  def predNum(x: LatticeObject): Int = x.size

  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]], p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject) = {
    import p._
    val flags = createBooleanVariables(width)
    for (i <- top.iterator)
      !! (flags(i) ==> asRelation(BitSet(i), xa, xb).head)
    (flags,
     flagValues => BitSet((for ((v, i) <- flagValues.iterator.zipWithIndex;
                                if (v)) yield i).toSeq : _*))
  }
}

////////////////////////////////////////////////////////////////////////////////

object TermSubsetLattice {
  def apply(termsCosts : Seq[(ITerm, Int)], name : String = "") = {
    val objseq = termsCosts.unzip._1.toIndexedSeq
    val cmap = termsCosts.toMap
    new TermSubsetLattice(objseq, cmap, name)
  }
  def apply(objseq: Seq[ITerm], cmap: Map[ITerm, Int]) = {
    new TermSubsetLattice(objseq, cmap, "")
  }
}

class TermSubsetLattice private (objseq: Seq[ITerm],
                                 costMap : Map[ITerm, Int],
                                 _name : String)
      extends BitSetLattice(objseq.size, _name) {

  assert(costMap.keySet == objseq.toSet)

  override def toString = "TermSubsetLattice: " + (objseq mkString ", ")

  val arity = 1

  protected def pp(bit : Int) : String = objseq(bit).toString

  private val bitCostMap =
    (for ((t, i) <- objseq.iterator.zipWithIndex) yield (i, costMap(t))).toMap

  protected def bitCost(bit : Int) : Int = bitCostMap(bit)

  def getTerms(obj : LatticeObject) : Iterator[ITerm] =
    for ((t, i) <- objseq.iterator.zipWithIndex; if (obj contains i)) yield t

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] = {
    import IExpression._
//    if (xa.isEmpty) return List(new IBoolLit(true))
    List(and(for ((t, i) <- objseq.iterator.zipWithIndex; if (obj contains i)) yield {
          subst(t, xa.head.toList, 0) === subst(t, xb.head.toList, 0)
        }))
  }

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
   List((asRelation(obj, xa, x).head, asRelation(obj, x, xb).head))

  //////////////////////////////////////////////////////////////////////////////

  private val term2Internal =
    (for (t <- objseq.iterator;
          intT = try {
            LinearCombination(InputAbsy2Internal(t, TermOrder.EMPTY),
                              TermOrder.EMPTY)
          } catch {
            // the term might contain operators that cannot directly
            // be translated to internal (like ite, eps)
            case _ : scala.MatchError => null
          };
          if (intT != null))
     yield (t -> intT)).toMap

  private val trivial =
    objseq forall (_.isInstanceOf[IVariable])

  private val cache = new LRUCache[LatticeObject, LatticeObject](10000)

  override def canonise(o : LatticeObject) : LatticeObject =
    if (trivial) {
      o
    } else cache(o) {
      import TerForConvenience._
      implicit val order = TermOrder.EMPTY

      val intTerms =
        (for (t <- getTerms(o);
              intT <- (term2Internal get t).iterator)
         yield intT).toList

      val reducer = ReduceWithEqs(intTerms === 0, order)
      val res = top filter { i => (o contains i) ||
                                  ((term2Internal get objseq(i)) exists {
                                     x => reducer(x).isZero
                                   }) }
//println("extending: size is " + res.size)
//println(o)
//println(res)
      res
    }

  // The reduced lattice corresponding to this lattice
  lazy val reducedLattice : AbsLattice =
    TermExtendingLattice(this)
}

////////////////////////////////////////////////////////////////////////////////

object TermIneqLattice {
  def apply(lowerBounds : Seq[(ITerm, Int)], name : String = "") =
    new TermIneqLattice(lowerBounds.unzip._1.toIndexedSeq,
                        lowerBounds.toMap,
                        name)
}

// Base case class
class TermIneqLattice private (lowerBounds: Seq[ITerm],
                               lowerCostMap : Map[ITerm, Int],
                               _name : String)
      extends BitSetLattice(lowerBounds.size, _name) {

  assert(lowerCostMap.keySet == lowerBounds.toSet)

  override def toString =
    "TermIneqLattice: " + lowerCostMap

  val arity = 1

  protected def pp(bit : Int) : String = " <= " + lowerBounds(bit)

  private val bitCostMap =
    (for ((t, i) <- lowerBounds.iterator.zipWithIndex)
     yield (i, lowerCostMap(t))).toMap

  protected def bitCost(bit : Int) : Int = bitCostMap(bit)

  def getTerms(obj : LatticeObject) : Iterator[ITerm] =
    for ((t, i) <- lowerBounds.iterator.zipWithIndex;
         if (obj contains i)) yield t

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] = {
    import IExpression._
//    if (xa.isEmpty) return List(new IBoolLit(true))
    List(and(for (t <- getTerms(obj)) yield {
            subst(t, xa.head.toList, 0) <= subst(t, xb.head.toList, 0)
        }))
  }

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
   List((asRelation(obj, xa, x).head, asRelation(obj, x, xb).head))

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice = this
}

////////////////////////////////////////////////////////////////////////////////

object PredicateLattice {
  def apply(predicateCosts : Seq[(IFormula, Int)], name : String = "") =
    new PredicateLattice(predicateCosts.unzip._1.toIndexedSeq,
                         predicateCosts.toMap,
                         name)
}

// Base case class
class PredicateLattice private (predicates: Seq[IFormula],
                                costMap : Map[IFormula, Int],
                                _name : String)
      extends BitSetLattice(predicates.size, _name) {

  assert(costMap.keySet == predicates.toSet)

  override def toString =
    "PredicateLattice: " + costMap

  val arity = 1

  protected def pp(bit : Int) : String = predicates(bit).toString

  private val bitCostMap =
    (for ((t, i) <- predicates.iterator.zipWithIndex) yield (i, costMap(t))).toMap

  protected def bitCost(bit : Int) : Int = bitCostMap(bit)

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] = {
    import IExpression._
//    if (xa.isEmpty) return List(new IBoolLit(true))
    List(and(for ((t, i) <- predicates.iterator.zipWithIndex; if (obj contains i)) yield {
          subst(t, xa.head.toList, 0) ==> subst(t, xb.head.toList, 0)
        }))
  }

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
   List((asRelation(obj, xa, x).head, asRelation(obj, x, xb).head))

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice = this
}

////////////////////////////////////////////////////////////////////////////////

abstract class ExtendingLattice[BaseLattice <: AbsLattice](val baseLattice : BaseLattice)
                               extends AbsLattice {

  type LatticeObject = baseLattice.LatticeObject

  def pp(o : LatticeObject) = baseLattice.pp(o)

  /**
   * Has to be defined as a monotonic, extending, idempotent function
   * on the base lattice
   */
  def extendObject(o : LatticeObject) : LatticeObject

  val latticeOrder = baseLattice.latticeOrder
  val top = baseLattice.top
  val bottom = baseLattice.bottom
  val arity = baseLattice.arity

  def join(x: LatticeObject, y: LatticeObject) =
    extendObject(baseLattice.join(x, y))
  def meet(x: LatticeObject, y: LatticeObject) =
    baseLattice.meet(x, y)

  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject = obj

  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject = { assert(false); bottom }

  def succ(x: LatticeObject): Iterator[LatticeObject] = {
    val returned = new MHashSet[LatticeObject]
    for (o <- baseLattice.succ(x);
         extendedO = extendObject(o);
         if (returned add extendedO)) yield extendedO
  }

  def succWithLimit(obj:LatticeObject, topEl:LatticeObject) : Iterator[LatticeObject] = {
    val returned = new MHashSet[LatticeObject];
    for (o <- baseLattice.succWithLimit(obj,topEl);
         extendedO = extendObject(o);
         if (returned add extendedO )) yield extendedO
  }

  protected def maximiseBelow(x : LatticeObject,
                              bound : LatticeObject) : LatticeObject = {
    val it = baseLattice.succ(x)
    while (it.hasNext) {
      val y = it.next
      if (latticeOrder.lt(y, bound)) {
        val extendedY = extendObject(y)
        if (latticeOrder.lt(extendedY, bound))
          return maximiseBelow(extendedY, bound)
      }
    }
    x
  }

  def pred(start: LatticeObject): Iterator[LatticeObject] = {
    val returned, explored = new MHashSet[LatticeObject]

//    def checkCorrectness(a : LatticeObject) =
//      assert(baseLattice.succ(a) forall {x => !latticeOrder.lteq(x, start) || extendObject(x) == start})

    def predHelp(x : LatticeObject) : Iterator[LatticeObject] = {
      for (y <- baseLattice.pred(x);
           if (explored add y);
           extendedY = extendObject(y);
           z <- {// println("x = " + x + "; y = " + y + "; extendedY = " + extendedY)
                 if (extendedY == start) {
                   predHelp(y)
                 } else if (extendedY == y) {
                   returned += y
                   Iterator single y
                 } else {
                   val maxiY = maximiseBelow(extendedY, start)
                   if (returned add maxiY)
                     Iterator single maxiY
                   else
                     Iterator.empty
                 }}) yield z
}

/*    println("computing pred for " + start)
    val res = predHelp(start).toList
    println(res)
    assert(
      (baseLattice.pred(start) forall { x => res exists { y => latticeOrder.lteq(y, x) } })
    )
    res.iterator */

    predHelp(start)
  }

  def predCheapestFirst(start: LatticeObject): Iterator[LatticeObject] =
    throw new UnsupportedOperationException

  def predRandom(x: LatticeObject)
                (implicit randGen : Random) : Iterator[LatticeObject] =
    throw new UnsupportedOperationException

/*  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] = {
    val returned = new MHashSet[LatticeObject]
    for (x <- baseLattice.incomparableBelow(topEl, comp);
         extendedX = {println(x); extendObject(x)};
         if ((returned add extendedX) &&
             latticeOrder.tryCompare(extendedX, comp) == None)) yield extendedX
  } */

  def predNum(x: LatticeObject): Int = baseLattice.predNum(x)
  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) =
    extendObject(baseLattice.middle(lower, upper))
  def cost(obj : LatticeObject) : Int = baseLattice.cost(obj)

  def asRelation(obj : LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] =
    baseLattice.asRelation(obj, xa, xb)

  def asRelation(obj : LatticeObject,  xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], 
                 xb : Seq[Seq[ITerm]]) : List[(IFormula, IFormula)] =
    baseLattice.asRelation(obj, xa, x, xb)

  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]], p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject) =
    throw new UnsupportedOperationException

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice = this
}

////////////////////////////////////////////////////////////////////////////////

case class TermExtendingLattice(_baseLattice : TermSubsetLattice)
                               extends ExtendingLattice(_baseLattice) {

  def extendObject(o : LatticeObject) : LatticeObject = baseLattice.canonise(o)

  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] = {
    val returned, explored = new MHashSet[LatticeObject]

//    def checkCorrectness(a : LatticeObject) =
//      assert(baseLattice.succ(a) forall {x => !latticeOrder.lteq(x, start) || extendObject(x) == start})

    def handlePred(y : LatticeObject) : Iterator[LatticeObject] = {
      val extendedY = extendObject(y)
      if (extendedY == topEl) {
        predHelp(y)
      } else if (extendedY == y) {
        returned += y
        Iterator single y
      } else {
        val maxiY = maximiseBelow(extendedY, topEl)
        if (returned add maxiY)
          Iterator single maxiY
        else
          Iterator.empty
      }
    }

    def predHelp(x : LatticeObject) : Iterator[LatticeObject] =
      for (y <- baseLattice.pred(x);
           if (explored add y);
           z <- handlePred(y)) yield z

/*    println("computing pred for " + start)
    val res = predHelp(start).toList
    println(res)
    assert(
      (baseLattice.pred(start) forall { x => res exists { y => latticeOrder.lteq(y, x) } })
    )
    res.iterator */

    for (t <- baseLattice.objseqCostlyFirst.iterator;
         if (comp contains t);
         y = topEl - t;
         if (explored add y);
         z <- handlePred(y);
         if (latticeOrder.tryCompare(z, comp) == None)) yield z
  }

}
