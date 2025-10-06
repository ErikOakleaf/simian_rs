An interpreter for the monkey programming language as defined by https://monkeylang.org/

Compiles to bytecode and runs in a VM all made in rust !

# Features
simian_rs extends the original Monkey language with some useful additional features.

### Mutable variables

Variables in simian_rs are mutable and can be reassigned after declaration:

``` monkey
let a = 0;
a = 1;
a
```

**Output:** 1

Closures can also capture and mutate variables from their surrounding scope:

``` monkey
let a = 0;
let f = fn() {
    a = 1;
}
f()
```

**Output:** 1

### While loops

simian_rs supports while loops for repeated execution:

``` monkey
let a = 0;
while (a < 10) {
 a = a + 1
}
a
```

**Output:** 10

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
