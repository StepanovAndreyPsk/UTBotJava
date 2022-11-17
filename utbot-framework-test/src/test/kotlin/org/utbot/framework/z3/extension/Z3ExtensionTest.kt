package org.utbot.framework.z3.extension

import com.microsoft.z3.*
import com.microsoft.z3.Context
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.*
import org.utbot.engine.z3.Z3Initializer
import org.junit.jupiter.api.Test
import soot.*
import soot.options.Options
import java.util.*
import kotlin.collections.HashMap

class Z3ExtensionTest : Z3Initializer() {

    @Test
    fun testArrayDefault() {
        Context().use { ctx ->
            val arraySort = ctx.mkArraySort(arrayOf(ctx.mkIntSort(), ctx.mkIntSort()), ctx.mkIntSort())
            val ourArray = ctx.mkConst("a", arraySort) as ArrayExpr

            val solver = ctx.mkSolver()

            solver.add(ctx.mkEq(ctx.mkInt(42), ctx.mkTermArray(ourArray))) //mkTermArray function!
            solver.check()
            val evalArray = solver.model.eval(ourArray)
            assertEquals("((as const (Array Int Int Int)) 42)", evalArray.toString())
        }
    }

    @Test
    fun testInt() {
        Context().use { ctx ->
            val a by ctx.declareInt()
            val b by ctx.declareInt()

            val solver = ctx.mkSolver().apply { add(a * a + b * b `=` 8) }

            assertEquals(Status.SATISFIABLE, solver.check())

            val (aVal, bVal) = solver.model
                .eval(a, b)
                .filterIsInstance<IntNum>()
                .map(IntNum::getInt)
                .also { list -> assertEquals(2, list.size) }

            assertEquals(8, aVal * aVal + bVal * bVal)
        }
    }

    @Test
    fun testReal() {
        Context().use { ctx ->
            val x by ctx.declareReal()

            val solver = ctx.mkSolver().apply {
                add((x * x - x * 4 + 3 `=` 0) and !(x `=` 3))
            }

            assertEquals(Status.SATISFIABLE, solver.check())

            val xVal = (solver.model.eval(x) as RatNum).let {
                it.bigIntNumerator.divide(it.bigIntDenominator).toDouble()
            }

            assertEquals(1.0, xVal, 1E-8)
        }
    }

    @Test
    fun testStrings() {
        Context().use { ctx ->
            val a by ctx.declareString()
            val b by ctx.declareString()
            val c by ctx.declareString()

            val solver = ctx.mkSolver().apply {
                add(a + b `=` "abcd")
                add(b + c `=` "cdef")
                add(!(b `=` ""))
            }

            assertEquals(Status.SATISFIABLE, solver.check())

            val (aVal, bVal, cVal) = solver.model
                .eval(a, b, c)
                .filterIsInstance<SeqExpr>()
                .map(SeqExpr::getString)
                .also { list -> assertEquals(3, list.size) }

            assertEquals("abcd", "$aVal$bVal")
            assertEquals("cdef", "$bVal$cVal")
            assertTrue(bVal.isNotBlank())
        }
    }

    @Test
    fun testArrays() {
        Context().use { ctx ->
            val x by ctx.declareInt()
            val y by ctx.declareInt()
            val a1 by ctx.declareIntArray()

            val solver = ctx.mkSolver().apply {
                add(a1[x] `=` x)
                add(a1.set(x, y) `=` a1)
            }

            assertEquals(Status.SATISFIABLE, solver.check())

            val (xVal, yVal) = solver.model
                .eval(x, y)
                .filterIsInstance<IntNum>()
                .map(IntNum::getInt)
                .also { list -> assertEquals(2, list.size) }

            assertTrue(xVal == yVal)
        }
    }

    @Test
    fun testList() {
        Context().use { ctx ->
            val type = ctx.mkListSort("intList", ctx.intSort)
            val l by ctx.declareList(type)

            val solver = ctx.mkSolver().apply {
                add(!(l `=` type.nil))
                add(type.headDecl(l) `=` 1)
                add(type.tailDecl(l) `=` type.consDecl(type.headDecl(l), type.nil))
            }

            assertEquals(Status.SATISFIABLE, solver.check())

            val lVal = solver.model.eval(l)

            assertEquals("(cons 1 (cons 1 nil))", "$lVal")
        }
    }

    private val boardSize = 9
    private val BLOCK_SIZE = 3

    @Test
    fun testSudoku() {
        val board = arrayOf(
            intArrayOf(8, 0, 0, 0, 0, 0, 0, 0, 0),
            intArrayOf(0, 0, 3, 6, 0, 0, 0, 0, 0),
            intArrayOf(0, 7, 0, 0, 9, 0, 2, 0, 0),
            intArrayOf(0, 5, 0, 0, 0, 7, 0, 0, 0),
            intArrayOf(0, 0, 0, 0, 4, 5, 7, 0, 0),
            intArrayOf(0, 0, 0, 1, 0, 0, 0, 3, 0),
            intArrayOf(0, 0, 1, 0, 0, 0, 0, 6, 8),
            intArrayOf(0, 0, 8, 5, 0, 0, 0, 1, 0),
            intArrayOf(0, 9, 0, 0, 0, 0, 4, 0, 0)
        ) // zero as an empty cell

        Context().use { ctx ->
            fun getSymName(row: Int, col: Int): String {
                return mutableListOf(row.toString(), col.toString()).joinToString("_")
            }
            var cells = mutableListOf<MutableList<IntExpr>>()
            for (i in 0 until boardSize) {
                val row = mutableListOf<IntExpr>()
                for (j in 0 until boardSize) {
                    row += ctx.mkIntConst(getSymName(i, j))
                }
                cells += row
            }

            val valueConstraints = mutableListOf<BoolExpr>()
            for (i in 0 until boardSize) {
                for (j in 0 until boardSize) {
                    valueConstraints += ctx.mkAnd(ctx.mkGe(cells[i][j], ctx.mkInt(1)), ctx.mkLe(cells[i][j], ctx.mkInt(9)))
                }
            }

            val distinctRowConstr = mutableListOf<BoolExpr>()
            for (i in 0 until boardSize) {
                distinctRowConstr += ctx.mkDistinct(*cells[i].map { it }.toTypedArray())
            }

            val distinctColConstr = mutableListOf<BoolExpr>()

            for (i in 0 until boardSize) {
                val col = mutableListOf<IntExpr>()
                for (j in 0 until boardSize) {
                    col += cells[j][i]
                }
                distinctColConstr += ctx.mkDistinct(*col.map { it }.toTypedArray())
            }

            val distinctBlockConstr = mutableListOf<BoolExpr>()
            for (i_block in 0 until BLOCK_SIZE) {
                for (j_block in 0 until BLOCK_SIZE) {
                    val block = mutableListOf<IntExpr>()
                    for (i in 0 until BLOCK_SIZE) {
                        for (j in 0 until BLOCK_SIZE) {
                            block += cells[i_block * 3 + i][j_block * 3 + j]
                        }
                    }
                    distinctBlockConstr += ctx.mkDistinct(*block.map { it }.toTypedArray())
                }
            }

            val sudokuConstr = valueConstraints + distinctRowConstr + distinctColConstr + distinctBlockConstr
            val inputConstr = mutableListOf<BoolExpr>()
            for (i in 0 until boardSize) {
                for (j in 0 until boardSize) {
                    if (board[i][j] != 0) {
                        inputConstr += ctx.mkEq(cells[i][j], ctx.mkInt(board[i][j]))
                    }
                }
            }
            val solver = ctx.mkSolver()
            val overallConstr = sudokuConstr + inputConstr
            solver.add(*overallConstr.map { it }.toTypedArray())
            if (solver.check().equals(Status.SATISFIABLE)) {
                for (i in 0 until boardSize) {
                    for (j in 0 until boardSize) {
                        print(solver.model.eval(cells[i][j]))
                        print(" ")
                    }
                    print("\n")
                }
            }
            else {
                println("couldn't solve")
            }
        }
    }

    @Test
    fun testSimpleTypeSystem() {
        Context().use { ctx ->
            val type = ctx.mkUninterpretedSort("Type");
            val func = HashMap<String, FuncDecl>()
            func["isSubtype"] = ctx.mkFuncDecl("isSubtype", arrayOf(type, type), ctx.boolSort)
            func["isSubclass"] = ctx.mkFuncDecl("isSubclass", arrayOf(type, type), ctx.boolSort);
            func["isSuperclass"] = ctx.mkFuncDecl("isSuperclass", arrayOf(type, type), ctx.boolSort);
            func["isInterface"] = ctx.mkFuncDecl("isInterface", type, ctx.boolSort);

            val types = HashMap<String, Expr>()
            types["Object"] = ctx.mkConst("Object", type)
            types["Collection"] = ctx.mkConst("Collection", type);
            types["Set"] = ctx.mkConst("Set", type);
            types["List"] = ctx.mkConst("List", type);
            types["Queue"] = ctx.mkConst("Queue", type);
            types["HashSet"] = ctx.mkConst("HashSet", type);
            types["ArrayList"] = ctx.mkConst("ArrayList", type);
            types["LinkedList"] = ctx.mkConst("LinkedList", type);
            types["PriorityQueue"] = ctx.mkConst("PriorityQueue", type);

            val isSubtype = func["isSubtype"]!!
            val isSubclass = func["isSubclass"]!!
            val isInterface = func["isInterface"]!!
            val x = ctx.mkSymbol("x")
            val y = ctx.mkSymbol("y")
            val z = ctx.mkSymbol("z")
            val xConst = ctx.mkConst(x, type)
            val yConst = ctx.mkConst(y, type)
            val zConst = ctx.mkConst(z, type)

            val reflect = ctx.mkForall(arrayOf(xConst), isSubtype.apply(xConst, xConst), 1, null, null, null ,null)
            val antisymmetry = ctx.mkForall(arrayOf(xConst, yConst), ctx.mkImplies(ctx.mkAnd(
                isSubtype.apply(xConst, yConst) as BoolExpr?, isSubtype(yConst, xConst) as BoolExpr?), ctx.mkEq(xConst, yConst)), 1, null, null, null, null)
            val transitivity = ctx.mkForall(arrayOf(xConst, yConst, zConst), ctx.mkImplies(ctx.mkAnd(
                isSubclass.apply(xConst, yConst) as BoolExpr?, isSubclass(yConst, zConst) as BoolExpr?), isSubclass(xConst, zConst) as BoolExpr?), 1, null, null, null, null)
            val interfaceIsNotSubclass = ctx.mkForall(arrayOf(xConst, yConst), ctx.mkImplies(
                ctx.mkAnd(ctx.mkNot(isInterface.apply(yConst) as BoolExpr?), isSubtype(xConst, yConst) as BoolExpr?, ctx.mkNot(ctx.mkEq(yConst, types["Object"]))),
                ctx.mkNot(isInterface(xConst) as BoolExpr?)
            ),
                1, null, null, null, null)
            val subclassEqSubtypeForNotInterfaces = ctx.mkForall(arrayOf(xConst, yConst), ctx.mkImplies(
                ctx.mkAnd(ctx.mkAnd(ctx.mkNot(isInterface.apply(xConst) as BoolExpr?), ctx.mkNot(isInterface.apply(yConst) as BoolExpr?))),
                ctx.mkEq(isSubclass.apply(xConst, yConst) as BoolExpr?, isSubtype(xConst, yConst))
            ),
                1, null, null, null, null)
            val solver = ctx.mkSolver()
            solver.add(reflect, antisymmetry, transitivity, interfaceIsNotSubclass, subclassEqSubtypeForNotInterfaces) // adding initial constraints

            val interfacesConstraints = ctx.mkAnd(
                isInterface.apply(types["Collection"]!!) as BoolExpr?,
                isInterface.apply(types["Set"]!!) as BoolExpr?,
                isInterface.apply(types["List"]!!) as BoolExpr?,
                isInterface.apply(types["Queue"]!!) as BoolExpr?,
                ctx.mkNot(isInterface.apply(types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isInterface.apply(types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isInterface.apply(types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isInterface.apply(types["PriorityQueue"]) as BoolExpr?)
            )

            solver.add(interfacesConstraints)

            val subtypeConstraints = ctx.mkAnd(
                isSubtype.apply(types["Set"], types["Collection"]) as BoolExpr?,
                isSubtype.apply(types["List"], types["Collection"]) as BoolExpr?,
                isSubtype.apply(types["Queue"], types["Collection"]) as BoolExpr?,
                isSubtype.apply(types["HashSet"], types["Set"]) as BoolExpr?,
                isSubtype.apply(types["ArrayList"], types["List"]) as BoolExpr?,
                isSubtype.apply(types["LinkedList"], types["List"]) as BoolExpr?,
                isSubtype.apply(types["LinkedList"], types["Queue"]) as BoolExpr?,
                isSubtype.apply(types["PriorityQueue"], types["Queue"]) as BoolExpr?,
                ctx.mkNot(isSubtype.apply(types["List"], types["Set"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Queue"], types["Set"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["ArrayList"], types["Set"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["LinkedList"], types["Set"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["PriorityQueue"], types["Set"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Collection"], types["Set"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["HashSet"], types["List"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["PriorityQueue"], types["List"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Collection"], types["List"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Set"], types["Queue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["List"], types["Queue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["HashSet"], types["Queue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["ArrayList"], types["Queue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Collection"], types["Queue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Collection"], types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Set"], types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["List"], types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Queue"], types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["ArrayList"], types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["LinkedList"], types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["PriorityQueue"], types["HashSet"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Collection"], types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Set"], types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["List"], types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Queue"], types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["HashSet"], types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["LinkedList"], types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["PriorityQueue"], types["ArrayList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Collection"], types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Set"], types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["List"], types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Queue"], types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["HashSet"], types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["ArrayList"], types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["PriorityQueue"], types["LinkedList"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Collection"], types["PriorityQueue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Set"], types["PriorityQueue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["List"], types["PriorityQueue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["Queue"], types["PriorityQueue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["HashSet"], types["PriorityQueue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["ArrayList"], types["PriorityQueue"]) as BoolExpr?),
                ctx.mkNot(isSubtype.apply(types["LinkedList"], types["PriorityQueue"]) as BoolExpr?)
            )

            solver.add(subtypeConstraints)

            if (solver.check().equals(Status.SATISFIABLE)) {
                println("OK")
            }
            else {
                println("couldn't solve")
            }
        }
    }

    @Test
    fun testSootHierarchy() {
        G.reset()
        Options.v().set_prepend_classpath(true)
        Options.v().set_allow_phantom_refs(true)
        Scene.v().loadNecessaryClasses()
        PackManager.v().runPacks()
        Scene.v().classes.forEach {
            if (it.resolvingLevel() < SootClass.HIERARCHY)
                it.setResolvingLevel(SootClass.HIERARCHY)
        }

        val hierarchy = Scene.v().orMakeFastHierarchy

//        val hierarchy = Scene.v().activeHierarchy
//        val obj = Scene.v().getSootClass("java.lang.Object")
//        assertNotNull(obj)
//        hierarchy.getDirectSubclassesOf(obj).forEach {
//            println(it.name)
//        }

        Context().use { ctx ->
            val func = HashMap<String, FuncDecl>()
            val type = ctx.mkUninterpretedSort("Type");
            func["isSubtype"] = ctx.mkFuncDecl("isSubtype", arrayOf(type, type), ctx.boolSort)
            func["isSubclass"] = ctx.mkFuncDecl("isSubclass", arrayOf(type, type), ctx.boolSort);
            func["isSuperclass"] = ctx.mkFuncDecl("isSuperclass", arrayOf(type, type), ctx.boolSort);
            func["isInterface"] = ctx.mkFuncDecl("isInterface", type, ctx.boolSort);

            val isSubtype = func["isSubtype"]!!
            val isSubclass = func["isSubclass"]!!
            val isInterface = func["isInterface"]!!
            val x = ctx.mkSymbol("x")
            val y = ctx.mkSymbol("y")
            val z = ctx.mkSymbol("z")
            val xConst = ctx.mkConst(x, type)
            val yConst = ctx.mkConst(y, type)
            val zConst = ctx.mkConst(z, type)

            val types = HashMap<String, Expr>()
            val obj = Scene.v().getSootClass("java.lang.Object")
            types[obj.name] = ctx.mkConst(obj.name, type)
            val reflect = ctx.mkForall(arrayOf(xConst), isSubtype.apply(xConst, xConst), 1, null, null, null ,null)
            val antisymmetry = ctx.mkForall(arrayOf(xConst, yConst), ctx.mkImplies(ctx.mkAnd(
                isSubtype.apply(xConst, yConst) as BoolExpr?, isSubtype(yConst, xConst) as BoolExpr?), ctx.mkEq(xConst, yConst)), 1, null, null, null, null)
            val transitivity = ctx.mkForall(arrayOf(xConst, yConst, zConst), ctx.mkImplies(ctx.mkAnd(
                isSubclass.apply(xConst, yConst) as BoolExpr?, isSubclass(yConst, zConst) as BoolExpr?), isSubclass(xConst, zConst) as BoolExpr?), 1, null, null, null, null)
            val interfaceIsNotSubclass = ctx.mkForall(arrayOf(xConst, yConst), ctx.mkImplies(
                ctx.mkAnd(ctx.mkNot(isInterface.apply(yConst) as BoolExpr?), isSubtype(xConst, yConst) as BoolExpr?, ctx.mkNot(ctx.mkEq(yConst, types["java.lang.Object"]))), // ?
                ctx.mkNot(isInterface(xConst) as BoolExpr?)
            ),
                1, null, null, null, null)
            val subclassEqSubtypeForNotInterfaces = ctx.mkForall(arrayOf(xConst, yConst), ctx.mkImplies(
                ctx.mkAnd(ctx.mkAnd(ctx.mkNot(isInterface.apply(xConst) as BoolExpr?), ctx.mkNot(isInterface.apply(yConst) as BoolExpr?))),
                ctx.mkEq(isSubclass.apply(xConst, yConst) as BoolExpr?, isSubtype(xConst, yConst))
            ),
                1, null, null, null, null)

            // additional constraints

            val solver = ctx.mkSolver()
            solver.add(reflect, antisymmetry, transitivity, interfaceIsNotSubclass, subclassEqSubtypeForNotInterfaces) // adding initial constraints


            val firstLayer = hierarchy.getSubclassesOf(obj)
            for (cl in firstLayer) {
                types[cl.name] = ctx.mkConst(cl.name, type)
            }

            // Adding not subtype constraints
            for (t1 in firstLayer) {
                for (t2 in firstLayer) {
                    if (!t1.name.equals(t2.name)) {
                        solver.add(ctx.mkNot(isSubtype.apply(types[t1.name], types[t2.name]) as BoolExpr?))
                        solver.add(ctx.mkNot(isSubtype.apply(types[t2.name], types[t1.name]) as BoolExpr?))
                    }
                }
            }

            // BFS
            val queue = ArrayDeque<SootClass>()
            queue.push(obj)
            var curClass = obj
            while (curClass != null) {
                if (!types.containsKey(curClass.name)) {
                    types[curClass.name] = ctx.mkConst(curClass.name, type)
                }
                if (curClass.isInterface) {
                    solver.add(isInterface.apply(types[curClass.name]) as BoolExpr?)
                    hierarchy.getAllSubinterfaces(curClass).forEach {
                        if (!types.containsKey(it.name)) {
                            types[it.name] = ctx.mkConst(it.name, type)
                        }
                        solver.add(isSubtype.apply(types[it.name], types[curClass.name]) as BoolExpr?)
                        queue.addFirst(it)
                    }
                }
                else {
                    solver.add(ctx.mkNot(isInterface.apply(types[curClass.name]) as BoolExpr?))
                    hierarchy.getSubclassesOf(curClass).forEach {
                        if (!types.containsKey(it.name)) {
                            types[it.name] = ctx.mkConst(it.name, type)
                        }
                        solver.add(isSubclass.apply(types[it.name], types[curClass.name]) as BoolExpr?)
                        queue.addFirst(it)
                    }
                }
                curClass = queue.pollLast()
            }

            if (solver.check().equals(Status.SATISFIABLE)) {
                println("OK")
            }
            else {
                println("couldn't solve")
            }

            // TODO : write some tests
        }
    }
}