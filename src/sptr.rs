pub trait Strict {
  fn addr(self) -> usize;
  fn expose_addr(self) -> usize;
  fn with_addr(self, addr: usize) -> Self;
}

macro_rules! impl_strict {
  ($($t:ty),*) => {
    $(impl<T> Strict for $t {
      #[inline]
      fn addr(self) -> usize { self as usize }
      #[inline]
      fn expose_addr(self) -> usize { self as usize }
      #[inline]
      fn with_addr(self, addr: usize) -> Self {
        // Implementation taken from the `sptr` crate.
        let self_addr = self.addr() as isize;
        let dest_addr = addr as isize;
        let offset = dest_addr.wrapping_sub(self_addr);
        self.cast::<u8>().wrapping_offset(offset).cast::<T>()
      }
    })*
  };
}

impl_strict!(*const T, *mut T);
