include "../util/collections.dfy"

module Machine {
    newtype {:nativeType "byte"} byte = x:int | 0 <= x < 256
    newtype {:nativeType "uint"} uint32 = x:int | 0 <= x < U32.MAX
    newtype {:nativeType "ulong"} uint64 = x:int | 0 <= x < U64.MAX

    predicate no_overflow(x: nat, y: int)
    {
        0 <= x + y < U64.MAX
    }

    function method sum_overflows(x: uint64, y: uint64): (overflow:bool)
        ensures !overflow == no_overflow(x as nat, y as nat)
    {
        // discovered by trial and error
        x > (0xFFFF_FFFF_FFFF_FFFF-y)
    }

    // NOTE(tej): I wanted this to be in module U64, but Dafny imports children
    // modules into their parents but not the other way around, so there's no
    // way to do that without making U64 a separate module (which I don't know
    // how to re-export)
    predicate no_overflow_u64(x: uint64, y: int)
    {
        no_overflow(x as nat, y)
    }

    function method min_u64(x: uint64, y: uint64): uint64
    {
        if x < y then x else y
    }

    lemma min_u64_lb(x: uint64, y: uint64)
        ensures min_u64(x, y) <= x && min_u64(x, y) <= y
    {}

    function method max_u64(x: uint64, y: uint64): uint64
    {
        if x > y then x else y
    }

    lemma max_u64_ub(x: uint64, y: uint64)
        ensures x <= max_u64(x, y) && y <= max_u64(x, y)
    {}

    module U64 {
        const MAX: nat := 0x1_0000_0000_0000_0000
    }

    module U32 {
        const MAX: nat := 0x1_0000_0000
    }
}

module {:extern "debug", "github.com/mit-pdos/dafny-jrnl/dafny_go/debug"} DebugPrint {
    method {:extern} Print(s: string)
}

module Debug
{
    import DebugPrint

    method Print(s: string)
    {
        DebugPrint.Print(s);
    }

    method Println(s: string)
    {
        DebugPrint.Print(s + "\n");
    }
}

module debug_test
{
    import opened Debug

    method test()
    {
        Println("hello world");
    }
}
