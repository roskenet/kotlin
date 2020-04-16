// !WITH_NEW_INFERENCE
// !DIAGNOSTICS: -UNUSED_VARIABLE, -UNUSED_PARAMETER -UNUSED_ANONYMOUS_PARAMETER

fun foo(i: Int) {}
fun foo(s: String) {}
fun foo2(i: Int) {}
fun foo3(i: Number) {}
fun <K> id(x: K): K = x
fun <K> id1(x: K): K = x
fun <L> id2(x: L): L = x
fun <T> baz1(x: T, y: T): T = TODO()
fun <T> baz2(x: T, y: Inv<T>): T = TODO()
fun <T> select(vararg x: T) = x[0]

class Inv<T>(val x: T)

fun test1() {
    val x1: (Int) -> Unit = id(id(::foo))
    val x2: (Int) -> Unit = baz1(id(::foo), ::foo)
    val x3: (Int) -> Unit = baz1(id(::foo), id(id(::foo)))
    val x4: (String) -> Unit = baz1(id(::foo), id(id(::foo)))

    id<(Int) -> Unit>(id(id(::foo)))
    id(id<(Int) -> Unit>(::foo))
    baz1<(Int) -> Unit>(id(::foo), id(id(::foo)))
    baz1(id(::foo), id(id<(Int) -> Unit>(::foo)))
    baz1(id(::foo), id<(Int) -> Unit>(id(::foo)))

    baz1(id { <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.Int")!>it<!>.inv() }, id<(Int) -> Unit> { })
    baz1(id1 { x -> <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.Int")!>x<!>.inv() }, id2 { x: Int -> })
    baz1(id1 { <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.Int")!>it<!>.inv() }, id2 { x: Int -> })

    baz2(id1 { <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.Int")!>it<!>.inv() }, id2(Inv { x: Int -> }))

    select(id1 { <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.Int")!>it<!>.inv() }, id1 { x: Number -> TODO() }, id1(id2 { x: Int -> x }))

    select(id1 { <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.Int")!>it<!>.inv() }, id1 { x: Number -> TODO() }, id1(id2(::foo2)))
    select(id1 { x: Inv<out Number> -> TODO() }, id1 { <!DEBUG_INFO_EXPRESSION_TYPE("Inv<kotlin.Int>")!>it<!>.x.inv() }, id1 { x: Inv<Int> -> TODO() })

    select(id1 { <!DEBUG_INFO_EXPRESSION_TYPE("{Inv<Int> & Inv<Number>}")!>it<!> }, id1 { x: Inv<Number> -> TODO() }, id1 { x: Inv<Int> -> TODO() })

    <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.reflect.KFunction1<kotlin.Int, kotlin.Unit>")!>select(id1(::foo), id(::foo3), id1(id2(::foo2)))<!>

    select({ <!DEBUG_INFO_EXPRESSION_TYPE("kotlin.Int")!>it<!> }, { x: Int -> TODO() })
}
