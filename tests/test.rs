use std::cmp::max;
use std::fmt::Debug;
use std::ptr::NonNull;
use ointers::*;
use rand::{thread_rng, rngs::ThreadRng, RngCore};
use rayon::prelude::*;
    
#[cfg(target_pointer_width="16")]
fn random_usize(rng: &mut ThreadRng) -> usize {
    let mut bytes = [0u8; 2];
    rng.fill_bytes(&bytes[..]);
    usize::from_native_bytes(bytes)
}

#[cfg(target_pointer_width="32")]
fn random_usize(rng: &mut ThreadRng) -> usize { rng.next_u32() as usize }

#[cfg(target_pointer_width="64")]
fn random_usize(rng: &mut ThreadRng) -> usize { rng.next_u64() as usize }

fn round_trip_ointer<T: Copy + Debug + Eq, const A: u8, const S: bool, const V: u8>(
    ptr: *mut T,
    val: T,
    theft: usize
) {
    let mask = mask(A + S as u8 + V);
    let stolen = theft & mask;
    let o: Ointer<T, A, S, V> = unsafe { Ointer::new(ptr) };
    assert_eq!(o.as_ptr(), ptr);
    assert_eq!(unsafe { o.as_ptr().read() }, val);
    assert_eq!(o.stolen(), 0);
    let p = o.steal(0);
    assert_eq!(p.as_ptr(), ptr);
    assert_eq!(unsafe { p.as_ptr().read() }, val);
    assert_eq!(p.stolen(), 0);
    let p = o.steal(theft);
    assert_eq!(p.as_ptr(), ptr);
    assert_eq!(unsafe { p.as_ptr().read() }, val);
    assert_eq!(p.stolen(), stolen);
    let p = o.steal(stolen);
    assert_eq!(p.as_ptr(), ptr);
    assert_eq!(unsafe { p.as_ptr().read() }, val);
    assert_eq!(p.stolen(), stolen);
    let p = o.steal(0);
    assert_eq!(p.as_ptr(), ptr);
    assert_eq!(unsafe { p.as_ptr().read() }, val);
    assert_eq!(p.stolen(), 0);
    let p = o.steal(usize::MAX);
    assert_eq!(p.as_ptr(), ptr);
    assert_eq!(unsafe { p.as_ptr().read() }, val);
    assert_eq!(p.stolen(), mask);
}

fn round_trip_not_null<T: Copy + Debug + Eq, const A: u8, const S: bool, const V: u8>(
    ptr: NonNull<T>,
    val: T,
    theft: usize
) {
    let mask = mask(A + S as u8 + V);
    let stolen = theft & mask;
    let o: NotNull<T, A, S, V> = unsafe { NotNull::new(ptr) };
    assert_eq!(o.as_non_null(), ptr);
    assert_eq!(unsafe { o.as_non_null().as_ptr().read() }, val);
    assert_eq!(o.stolen(), 0);
    let p = o.steal(0);
    assert_eq!(p.as_non_null(), ptr);
    assert_eq!(unsafe { p.as_non_null().as_ptr().read() }, val);
    assert_eq!(p.stolen(), 0);
    let p = o.steal(theft);
    assert_eq!(p.as_non_null(), ptr);
    assert_eq!(unsafe { p.as_non_null().as_ptr().read() }, val);
    assert_eq!(p.stolen(), stolen);
    let p = o.steal(stolen);
    assert_eq!(p.as_non_null(), ptr);
    assert_eq!(unsafe { p.as_non_null().as_ptr().read() }, val);
    assert_eq!(p.stolen(), stolen);
    let p = o.steal(0);
    assert_eq!(p.as_non_null(), ptr);
    assert_eq!(unsafe { p.as_non_null().as_ptr().read() }, val);
    assert_eq!(p.stolen(), 0);
    let p = o.steal(usize::MAX);
    assert_eq!(p.as_non_null(), ptr);
    assert_eq!(unsafe { p.as_non_null().as_ptr().read() }, val);
    assert_eq!(p.stolen(), mask);
}

macro_rules! rt_ointer {
    ($value:expr, $ptr:expr, $theft:expr, $type:ty, $v:literal) => {
        round_trip_ointer::<$type, 0, false, $v>($ptr, $value, $theft);
        round_trip_ointer::<$type, 1, false, $v>($ptr, $value, $theft);
        round_trip_ointer::<$type, 2, false, $v>($ptr, $value, $theft);
        round_trip_ointer::<$type, 3, false, $v>($ptr, $value, $theft);
        round_trip_ointer::<$type, 0, true,  $v>($ptr, $value, $theft);
        round_trip_ointer::<$type, 1, true,  $v>($ptr, $value, $theft);
        round_trip_ointer::<$type, 2, true,  $v>($ptr, $value, $theft);
        round_trip_ointer::<$type, 3, true,  $v>($ptr, $value, $theft);
    }
}

macro_rules! rt_not_null {
    ($value:expr, $ptr:expr, $theft:expr, $type:ty, $v:literal) => {
        round_trip_not_null::<$type, 0, false, $v>($ptr, $value, $theft);
        round_trip_not_null::<$type, 1, false, $v>($ptr, $value, $theft);
        round_trip_not_null::<$type, 2, false, $v>($ptr, $value, $theft);
        round_trip_not_null::<$type, 3, false, $v>($ptr, $value, $theft);
        round_trip_not_null::<$type, 0, true,  $v>($ptr, $value, $theft);
        round_trip_not_null::<$type, 1, true,  $v>($ptr, $value, $theft);
        round_trip_not_null::<$type, 2, true,  $v>($ptr, $value, $theft);
        round_trip_not_null::<$type, 3, true,  $v>($ptr, $value, $theft);
    }
}

#[test]
fn round_trip_ointer_locals() {
    (0..1_000_000).into_par_iter().for_each(|_| {
        let mut rng = thread_rng();
        let mut a: usize = random_usize(&mut rng);
        let theft = random_usize(&mut rng);
        rt_ointer!(a, &mut a as &mut usize, theft, usize, 0);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 1);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 2);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 3);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 4);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 5);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 6);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 7);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 8);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 9);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 10);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 11);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 12);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 13);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 14);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 15);
        #[cfg(target_pointer_width="64")] rt_ointer!(a, &mut a as *mut usize, theft, usize, 16);
    })
}

#[test]
fn round_trip_ointer_boxes() {
    (0..1_000_000).into_par_iter().for_each(|_| {
        let mut rng = thread_rng();
        let a = Box::into_raw(Box::new(random_usize(&mut rng)));
        let theft = random_usize(&mut rng);
        unsafe {
            rt_ointer!(a.read(), a, theft, usize, 0);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 1);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 2);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 3);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 4);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 5);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 6);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 7);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 8);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 9);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 10);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 11);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 12);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 13);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 14);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 15);
            #[cfg(target_pointer_width="64")] rt_ointer!(a.read(), a, theft, usize, 16);
            Box::from_raw(a);
        }
    })
}

#[test]
fn round_trip_not_null_locals() {
    (0..1_000_000).into_par_iter().for_each(|_| {
        let mut rng = thread_rng();
        let mut a: usize = random_usize(&mut rng);
        let b = unsafe { NonNull::new_unchecked(&mut a as *mut usize) };
        let theft = random_usize(&mut rng);
        rt_not_null!(a, b, theft, usize, 0);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 1);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 2);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 3);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 4);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 5);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 6);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 7);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 8);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 9);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 10);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 11);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 12);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 13);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 14);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 15);
        #[cfg(target_pointer_width="64")] rt_not_null!(a, b, theft, usize, 16);
    })
}

#[test]
fn round_trip_not_null_boxes() {
    (0..1_000_000).into_par_iter().for_each(|_| {
        let mut rng = thread_rng();
        let a = Box::into_raw(Box::new(random_usize(&mut rng)));
        let b = unsafe { NonNull::new_unchecked(a) };
        let theft = random_usize(&mut rng);
        unsafe {
            rt_not_null!(a.read(), b, theft, usize, 0);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 1);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 2);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 3);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 4);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 5);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 6);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 7);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 8);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 9);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 10);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 11);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 12);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 13);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 14);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 15);
            #[cfg(target_pointer_width="64")] rt_not_null!(a.read(), b, theft, usize, 16);
            Box::from_raw(a);
        }
    })
}

fn mask(n: u8) -> usize {
    (isize::MIN >> (max(n, 1) - 1)) as usize
}
