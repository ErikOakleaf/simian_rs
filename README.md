An interpreter for the monkey programming language as defined by https://monkeylang.org/

Compiles to bytecode and runs in a VM all made in rust !

# Features

simian_rs extends the original Monkey language with some useful additional features.

## Mutable variables

Variables in simian_rs are mutable and can be reassigned after declaration:

```monkey
let a = 0;
a = 1;
a
```

**Output:** 1

Closures can also capture and mutate variables from their surrounding scope:

```monkey
let f = fn() {
    let a = 0;

    let b = fn() {
        a = 1;
    };

    b();
    a
}
f();
```

**Output:** 1

## While loops

simian_rs supports while loops for repeated execution:

```monkey
let a = 0;
while (a < 10) {
    a = a + 1
}
a
```

**Output:** 10

continues and breaks can also be used in while loops

```monkey

let count = 0;
let sum = 0;

while (count < 20) {
    count = count + 1;

    // Skip odd numbers using continue (check if divisible by 2)
    if (count / 2 * 2 != count) {
        continue;
    }

    // Stop at 15 using break
    if (count > 15) {
        break;
    }

    // Only even numbers from 2 to 14 reach here
    sum = sum + count;
}

sum
```

**Output:** 56

## Extended builtins

In addition to the built-in functions provided by the Monkey programming language, simian_rs includes additional built-ins for further functionality.

### append(array, value)

append is the counterpart to push, where push will create a copy of the array with the new value added append will modify the array that is given to it

```monkey
let a = [1];
append(a, 2);
a;
```

**Output:** [1, 2]

### insert(array/hash, integer/key, value)

inserts into an array or a hash at a specific index or key

```monkey
let a = [1 ,3]; 
insert(a, 1, 2); 
a;
```

**Output:** [1, 2, 3]


```monkey
let a = { "hello" : "world"}; 
insert(a, "one", "two"); 
a;
```

**Output:** { "hello" : "world", "one" : "two" }

### remove(array/hash, index/key)

removes the value at a given index or key in an array or hash

```monkey
let a = [1, 2, 3];
remove(a, 1);
a;
```

**Output:** [1, 3]

```monkey
let a = { "hello" : "world", "one" : "two"};
remove(a, "one");
a;
```

**Output:** { "hello" : "world" }

### pop(array)

pop's the last value of the array

```monkey
let a = [1, 2, 3];
pop(a);
```

**Output:** 3

### clone(array)

gives a clone of an array

```monkey
let a = [1, 2, 3];
let b = clone(a);
remove(a, 2);
b;
```

**Output:** [1, 2, 3]

# Benchmarks

For comparison with Thorsten Ball’s excellent teaching implementation of a monkey VM (from _Writing a Compiler in Go_), when executing this monkey code on my hardware:

```monkey
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
