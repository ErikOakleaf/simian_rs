An interpreter for the monkey programming language as defined by https://monkeylang.org/

Compiles to bytecode and runs in a VM all made in rust !

# Benchmarks

For comparison with Thorsten Ball’s excellent teaching implementation of a monkey VM (from *Writing a Compiler in Go*), when executing this monkey code on my hardware:

``` monkey
let fibonacci = fn(x) {
    if (x == 0) {
        0
    } else {
        if (x == 1) {
            return 1;
        } else {
            fibonacci(x - 1) + fibonacci(x - 2);
        }
    }
};
fibonacci(35);
```

simian_rs runs in 3.3 s and Thorsten Balls implementation runs in 5.8 s, which means simian_rs is 76 % faster in this case.
