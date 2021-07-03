//! What do you call a pointer we stole the high bits off? An ointer.
//!
//! Ointers is a library for representing pointers where some bits have
//! been stolen so that they may be used by the programmer for something
//! else. In effect, it's a small amount of free storage
//!
//! Fully supports no_std, dependency-free.
//!
//! Ointers supports a handful of bit sources. It's up to you to determine
//! when it is safe to use them.
//!
//! ## Alignment bits (const parameter A)
//!
//! If we know that a pointer's address will always be aligned to `A`
//! bytes where A > 1, we can steal log2(A-1) bytes. For an 8-byte aligned
//! value, this provides a modest 3 bits.
//!
//! If you have values aligned to some larger width, you could get even
//! more. It's common in parallel programming to pad data to a cache line
//! by increasing its alignment requirements in order eliminate false
//! sharing. Because a cache line on amd64 or aarch64 is effectively 128
//! bytes thanks to prefetching, you can reclaim a respectable 7 extra
//! bits.
//!
//! If your data is aligned wider still, the sky is the limit, but you
//! could get an incredible 24 bits if you have 16MB-aligned data!
//! Remember that the only alignment rust knows about is what is
//! declared for the type, so you must create a newtype wrapper to
//! take full advantage of large alignment sizes.
//!
//! | Bits | Min alignment |
//! |------|---------------|
//! | 1    |            2b |
//! | 2    |            4b |
//! | 3    |            8b |
//! | 4    |           16b |
//! | 5    |           32b |
//! | 6    |           64b |
//! | 7    |          128b |
//! | 8    |          256b |
//! | 9    |          512b |
//! | 10   |            1k |
//! | 11   |            2k |
//! | 12   |            4k |
//! | 13   |            8k |
//! | 14   |           16k |
//! | 15   |           32k |
//! | 16   |           64k |
//! | 17   |          128k |
//! | 18   |          256k |
//! | 19   |          512k |
//! | 20   |            1m |
//! | 21   |            2m |
//! | 22   |            4m |
//! | 23   |            8m |
//! | 24   |           16m |
//!
//! Stealing bits from alignment is relatively innocuous, but we can only
//! get the compiler to check it for you in dev mode as things stand in
//! rust today.
//!
//! ## Sign bit (parameter S)
//!
//! The most commonly used operating systems arrange memory so that the
//! high half of virtual memory space is reserved for the kernel and the
//! low half is given to userspace.
//!
//! Looked at as a signed integer, this makes the kernel half of address
//! space negative and the userspace half positive.
//!
//! Most programs do not deal with kernel addresses, thus giving us an
//! extra bit to play with.
//!
//! We can also get this extra bit in kernel mode if we know we will not
//! be dealing with userspace addresses. We do this by taking a pointer to
//! a value on the stack and stealing its sign bit.
//!
//! If you know you will be dealing with userspace addresses in kernel
//! space or kernel space addresses in userspace, or you are using or
//! implementing a kernel which does not follow this convention, you must
//! set `S` to `false`.
//!
//! The S bit is currently only tested with userspace pointers in
//! userspace. While we think it should work more generally, we currently
//! haven't got a test rig for other scenarios so we can't promise it does.
//!
//! ## Unused virtual address space (V)
//!
//! In 64-bit mode, address space is plentiful: nobody has 64 bits' worth
//! of RAM and even if they did, their processor is unable to address it
//! all. V is required to be 0 unless compiling for a 64bit target.
//!
//! The number of bits that may be safely stolen by this method depends
//! upon the microarchitecture in question and the page table depth.
//!
//! For x86-64 and aarch64, the following sizes apply:
//!
//! | Bits | PT depth | Support                           |
//! |------|----------|-----------------------------------|
//! | 25   |        3 | aarch64 only, uncommon, opt-in    |
//! | 16   |        4 | most common default               |
//! | 7    |        5 | some intel only, uncommon, opt-in |
//!
//! If you are made of money and need more than 128TB virtual address
//! space, you should limit yourself to 7 bits for V. Likewise if you know
//! you'll be on 3-deep page tables, you can steal a whopping 25 bits. But
//! you're probably limited to 16 bits in general.

#![no_std]
use core::marker::PhantomData;
use core::mem::align_of;
use core::ptr::NonNull;

/// A pointer we stole the high bits off
///
/// T: type pointed to.
/// A: number of bits to steal based on the alignment requirements of T.
/// S: whether to steal the sign bit.
/// V: number of bits to steal from unused virtual address space.

#[derive(Debug,Eq,Hash,PartialEq)]
#[repr(transparent)]
pub struct Ointer<T, const A: u8, const S: bool, const V: u8> {
    ptr: usize,
    _phantom: PhantomData<*mut T>,
}

impl<T: Sized, const A: u8, const S: bool, const V: u8> Clone for Ointer<T, A, S, V> {
    fn clone(&self) -> Self { Ointer { ptr: self.ptr, _phantom: PhantomData } }
}

impl<T: Sized, const A: u8, const S: bool, const V: u8> Copy for Ointer<T, A, S, V> {}

impl<T: Sized, const A: u8, const S: bool, const V: u8> Ointer<T, A, S, V> {
    /// Creates a new Ointer from a presumed legitimate pointer.
    ///
    /// # Safety
    ///
    /// * T's alignment must enable stealing A bits.
    /// * The high bits (sign upwards) must match a stack pointer's high bits.
    /// * If compiling for a 64bit arch, V must be at most 25.
    /// * If compiling for a non-64bit arch, V must be 0.
    ///
    /// These invariants are checked with `debug_assert` only, hence
    /// `unsafe`. The usual caveats of pointers apply.
    pub unsafe fn new(ptr: *mut T) -> Self {
        Ointer { ptr: pack(ptr, A, S, V), _phantom: PhantomData }
    }

    /// Returns the stolen bits in the high pos.
    pub fn stolen(self) -> usize { self.ptr as usize & asv_mask(A, S, V) }

    /// Takes a value from the high bits of the provided usize and
    /// steals them from the ointer.
    pub fn steal(self, bits: usize) -> Self {
        let mask = asv_mask(A, S, V);
        let bits = bits & mask;
        let ptr = self.ptr & !mask;
        Self { ptr: (ptr | bits), _phantom: PhantomData }
    }

    /// Get the pointer without the stolen bits
    pub fn as_ptr(self) -> *mut T {
        unsafe { unpack(self.ptr, A, S, V) as *mut T }
    }

    /// Direct access to the underlying data. The pointer it returns
    /// may not be valid.
    pub fn raw(self) -> *mut T { self.ptr as *mut T }

}

/// A non-null pointer that we stole the high bits off.
///
/// T: type pointed to.
/// V: number of bits to steal directly by masking them off.
/// A: number of bits to steal based on the alignment requirements of T.
#[derive(Debug,Eq,Hash,PartialEq)]
#[repr(transparent)]
pub struct NotNull<T, const A: u8, const S: bool, const V: u8>(NonNull<T>);

impl<T: Sized, const A: u8, const S: bool, const V: u8> Clone for NotNull<T, A, S, V> {
    fn clone(&self) -> Self { NotNull(self.0) }
}

impl<T: Sized, const A: u8, const S: bool, const V: u8> Copy for NotNull<T, A, S, V> {}

impl<T: Sized, const A: u8, const S: bool, const V: u8> NotNull<T, A, S, V> {
    /// Creates a new Ointer from a presumed legitimate pointer.
    ///
    /// # Safety
    ///
    /// * T's alignment must enable stealing A bits.
    /// * The high bits (sign upwards) must match a stack pointer's high bits.
    /// * If compiling for a 64bit arch, V must be at most 25.
    /// * If compiling for a non-64bit arch, V must be 0.
    ///
    /// These invariants are checked with `debug_assert` only, hence
    /// `unsafe`. The usual caveats of pointers apply.
    pub unsafe fn new(ptr: NonNull<T>) -> Self {
        let ptr = pack(ptr.as_ptr(), A, S, V) as *mut T;
        NotNull(NonNull::new_unchecked(ptr as *mut T))
    }


    /// Returns the stolen bits in the high pos.
    pub fn stolen(self) -> usize { self.0.as_ptr() as usize & asv_mask(A, S, V) }

    /// Takes a value from the high bits of the provided usize and
    /// steals them from the ointer.
    pub fn steal(self, bits: usize) -> Self {
        let mask = asv_mask(A, S, V);
        let bits = bits & mask;
        let ptr = self.raw() & !mask;
        Self(unsafe { NonNull::new_unchecked((ptr | bits) as *mut T) })
    }

    /// Get the pointer without the stolen bits
    pub fn as_non_null(self) -> NonNull<T> {
        unsafe { NonNull::new_unchecked(unpack(self.raw(), A, S, V)) }
    }

    /// Direct access to the underlying data. The pointer it returns
    /// may not be valid.
    pub fn raw(self) -> usize { self.0.as_ptr() as usize }

}

/// Packs a pointer into the bottom `sizeof(usize) - (a + s + v)` bits of a usize.
///
/// # Safety
///
/// * T's alignment must enable stealing A bits.
/// * The high bits (sign upwards) must match a stack pointer's high bits.
/// * If compiling for a 64bit arch, V must be at most 25.
/// * If compiling for a non-64bit arch, V must be 0.
///
/// These invariants are checked with `debug_assert` only, hence
/// `unsafe`. The usual caveats of pointers apply.
pub unsafe fn pack<T: Sized>(ptr: *mut T, a: u8, s: bool, v: u8) -> usize {
    let sv = asv_mask(0, s, v);
    #[cfg(debug_assertions)]
    {
        debug_assert!((1 << a) <= align_of::<T>());
        #[cfg(not(target_pointer_width="64"))]
        debug_assert!(v == 0);
        debug_assert!(v <= 25);
        // If S is set, the user has indicated they will never be
        // dealing with foreign pointers, so we can check that
        // too. We need only really check the sign bit because of
        // canonicalisation, but it's actually cheaper to check
        // all the high bits.
        if s {
            // We don't want to take account of A yet as the pointer
            // is still in its undoctored state.
            let ptr = ptr as usize;
            let stack = (&ptr as *const usize) as usize;
            // the top bits should match
            debug_assert!((sv & ptr) == (sv & stack));
        }
    }
    (ptr as usize & !sv) >> a as usize
}


/// Turns the `sizeof(usize) - (a + s + v)` bits of a usize (as
/// returned from `pack`) back into a pointer.
///
/// # Safety
///
/// The pointer must be of the correct type, otherwise you're
/// basically unsafely casting the pointer.
///
/// You must use the same settings as you packed the pointer with. The
/// pointer must be packed into the lower bits. Not strictly unsafe,
/// but indicative of a bug in your program.
pub unsafe fn unpack<T: Sized>(packed: usize, a: u8, s: bool, v: u8) -> *mut T {
    // Mask off all the stolen bits to get the pointer data.
    let asv = asv_mask(a, s, v);
    let masked = packed & !asv;
    // Restore the empty alignment bits
    let base = masked << a;
    if s {
        // Copy the top bits of a stack pointer
        let sv = asv_mask(0, s, v);
        let base = base as usize & !sv;
        let stack = (&base as *const usize) as usize & sv;
        (stack | base) as *mut T
    } else {
        // We need to extend the sign bit.
        (((base << v as usize) as isize) >> v as usize) as *mut T
    }
}

/// Produces a mask where the stolen bits (at the top) are set
pub const fn asv_mask(a: u8, s: bool, v: u8) -> usize { mask(a + s as u8 + v) }

/// Produces a mask where the stolen bits (at the top) are set
pub const fn mask(bits: u8) -> usize { (isize::MIN >> (max(bits as usize,1) - 1)) as usize }

// core::cmp::max isn't a const fn
const fn max(x: usize, y: usize) -> usize {
    if x <= y { y } else { x }
}
