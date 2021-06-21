[![License](https://img.shields.io/crates/l/ointers.svg)](https://github.com/irrustible/ointers/blob/main/LICENSE)
[![Package](https://img.shields.io/crates/v/ointers.svg)](https://crates.io/crates/ointers)
[![Documentation](https://docs.rs/ointers/badge.svg)](https://docs.rs/ointers)

# ointers

What do you call a pointer with the high bits stolen? An ointer!

Ointers is a library for representing pointers where some bits have
been stolen so that they may be used by the programmer for something
else. In effect, it's a small amount of free storage

Fully supports no_std, dependency-free, <100loc.

## Bit sources

Ointers supports a handful of bit sources. It's up to you to determine
when it is safe to use them.

### Alignment bits (const parameter A)

If we know that a pointer's address will always be aligned to `A`
bytes where A > 1, we can steal log2(A-1) bytes. For an 8-byte aligned
value, this provides a modest 3 bits.

If you have values aligned to some larger width, you could get even
more. It's common in parallel programming to pad data to a cache line
by increasing its alignment requirements in order eliminate false
sharing. Because a cache line on amd64 or aarch64 is effectively 128
bytes thanks to prefetching, you can reclaim a respectable 7 extra
bits.

If your data is aligned wider still, the sky is the limit, but you
could get an incredible 24 bits if you have 16MB-aligned data!
Remember that the only alignment rust knows about is what is declared
for the type, so you must create a newtype wrapper to take full
advantage of large alignment sizes.

| Bits | Min alignment |
|------|---------------|
| 1    |            2b |
| 2    |            4b |
| 3    |            8b |
| 4    |           16b |
| 5    |           32b |
| 6    |           64b |
| 7    |          128b |
| 8    |          256b |
| 9    |          512b |
| 10   |            1k |
| 11   |            2k |
| 12   |            4k |
| 13   |            8k |
| 14   |           16k |
| 15   |           32k |
| 16   |           64k |
| 17   |          128k |
| 18   |          256k |
| 19   |          512k |
| 20   |            1m |
| 21   |            2m |
| 22   |            4m |
| 23   |            8m |
| 24   |           16m |

Stealing bits from alignment is relatively innocuous, but we can only
get the compiler to check it for you in dev mode as things stand in
rust today.

### Sign bit (parameter S)

The most commonly used operating systems arrange memory so that the
high half of virtual memory space is reserved for the kernel and the
low half is given to userspace.

Looked at as a signed integer, this makes the kernel half of address
space negative and the userspace half positive.

Most programs do not deal with kernel addresses, thus giving us an
extra bit to play with.

We can also get this extra bit in kernel mode if we know we will not
be dealing with userspace addresses. We do this by taking a pointer to
a value on the stack and stealing its sign bit.

If you know you will be dealing with userspace addresses in kernel
space or kernel space addresses in userspace, or you are using or
implementing a kernel which does not follow this convention, you must
set `S` to `false`.

The S bit is currently only tested with userspace pointers in
userspace. While we think it should work more generally, we currently
haven't got a test rig for other scenarios so we can't promise it does.

### Unused virtual address space (V)

In 64-bit mode, address space is plentiful: nobody has 64 bits' worth
of RAM and even if they did, their processor is unable to address it
all. V is required to be 0 unless compiling for a 64bit target.

The number of bits that may be safely stolen by this method depends
upon the microarchitecture in question and the page table depth.

For x86-64 and aarch64, the following sizes apply:

| Bits | PT depth | Support                           |
|------|----------|-----------------------------------|
| 25   |        3 | aarch64 only, uncommon, opt-in    |
| 16   |        4 | most common default               |
| 7    |        5 | some intel only, uncommon, opt-in |

If you are made of money and need more than 128TB virtual address
space, you should limit yourself to 7 bits for V. Likewise if you know
you'll be on 3-deep page tables, you can steal a whopping 25 bits. But
you're probably limited to 16 bits in general.

## Hacking

Contributions welcome, please be nice.

The test suite requires std at present (because of rand's
ThreadRng). It takes about 36 seconds on my Ryzen 3900X. If you're on
a slower machine, you might want to reduce the loop iterations. It
should really only take one to shake most bugs out and a handful to
shake out the rest. The million iterations is just overkill to be sure
that's conveniently enabled by the incredible ease-of-use of rayon.

The tests are extensive. The number of configurations I'm currently
testing against is limited, however:

* x86-64, linux with 4PT

We would like to support more. These should be easy:

* x86, linux with 4PT should be possible through github actions.
* aarch64, linux with 4PT shouldn't be too hard to find access to.
* 32-bit arm (3PT) should be doable as well.

These will likely be harder:

* aarch64, linux with 3PT is probably not widely deployed
* Intel's new 5PT is of incredibly niche interest - if you want us to
  test it, you'll have to sponsor it because I don't have access to
  the hardware..

## Changelog

### v2.0.0

New APIS:

* `pack()` - packs a pointer into the low bits of a usize.
* `unpack()` - reverse of pack.
* `asv_mask()` - calculates a mask where the stolen bits are set on by a, s, v
* `asv_mask()` - calculates a mask where the stolen bits are set on by total bits
* `Ointer::raw()` - returns the raw data in the ointer (stolen + ptr) as a usize
* `NotNull::raw()` - same, but for NotNull

Changes:

* `Ointer` now uses a usize internally.

## Copyright and License

Copyright (c) 2021 James Laver, ointers contributors.

[Licensed](LICENSE) under Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0),
with LLVM Exceptions (https://spdx.org/licenses/LLVM-exception.html).

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
licensed as above, without any additional terms or conditions.
